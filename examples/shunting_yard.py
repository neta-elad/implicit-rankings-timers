from prelude import *

# taken from an old dijkstra note, see Manna & Dershovitz paper
# loop until the shunting yard is empty
# select a train
# if the train consists of only a single car
# then remove it from the yard
# else split it into two shorter trains
# fi
# repeat


# maybe we need to add the order on train in the model
# because we want the rank to be the number of cars in train - 1 and i dont know how to do that.


class Train(Finite): ...


class Car(Finite): ...


class ShuntingYard(TransitionSystem):
    car_in_train: Rel[Car, Train]
    train_in_yard: Rel[Train]
    car_order_in_train: Rel[Train, Car, Car]

    @init
    def car_order_is_order(self, t: Train, c1: Car, c2: Car, c3: Car) -> BoolRef:
        # the order of cars in a train is a total order (mutable)
        return And(
            # reflexivity
            Implies(
                self.car_in_train(c1, t),
                self.car_order_in_train(t, c1, c1),
            ),
            # antisymmetry
            Implies(
                And(
                    self.car_in_train(c1, t),
                    self.car_in_train(c2, t),
                    self.car_order_in_train(t, c1, c2),
                    self.car_order_in_train(t, c2, c1),
                ),
                c1 == c2,
            ),
            # transitivity
            Implies(
                And(
                    self.car_in_train(c1, t),
                    self.car_in_train(c2, t),
                    self.car_in_train(c3, t),
                    self.car_order_in_train(t, c1, c2),
                    self.car_order_in_train(t, c2, c3),
                ),
                self.car_order_in_train(t, c1, c3),
            ),
            # total
            Implies(
                And(
                    self.car_in_train(c1, t),
                    self.car_in_train(c2, t),
                ),
                Or(
                    self.car_order_in_train(t, c1, c2),
                    self.car_order_in_train(t, c2, c1),
                ),
            ),
            # if in order then in train
            Implies(
                self.car_order_in_train(t, c1, c2),
                And(
                    self.car_in_train(c1, t),
                    self.car_in_train(c2, t),
                ),
            ),
        )

    @init
    def in_yard_has_car(self, t: Train) -> BoolRef:
        c = Car("c")
        return Exists(c, self.car_in_train(c, t))

    @transition
    def split_train(self, train: Train, new_train: Train, split_car: Car) -> BoolRef:
        # an existing train in the yard is split into two shorter trains,
        # where the new train was previously empty, and not in yard
        # the split is such that all larger than split_car are in the new train (including)
        c = Car("c")
        c1 = Car("c1")
        c2 = Car("c2")
        t = Train("t")
        return And(
            # train is in the yard
            self.train_in_yard(train),
            # new train is empty
            ForAll(c, Not(self.car_in_train(c, new_train))),
            # new train is not in the yard
            Not(self.train_in_yard(new_train)),
            # split_car in train
            self.car_in_train(split_car, train),
            # split_car is not minimal in train
            Exists(
                c, And(self.car_order_in_train(train, c, split_car), c != split_car)
            ),
            ForAll(
                [c, t],
                self.next.car_in_train(c, t)
                == If(
                    # in train will be all cars < split_car from train
                    t == train,
                    And(
                        self.car_in_train(c, train),
                        self.car_order_in_train(train, c, split_car),
                        c != split_car,
                    ),
                    # in new_train will be all cars >= split_car from train
                    If(
                        t == new_train,
                        And(
                            self.car_in_train(c, train),
                            self.car_order_in_train(train, split_car, c),
                        ),
                        self.car_in_train(c, t),
                    ),
                ),
            ),
            # the order in any train is projected to those cars in the train
            ForAll(
                [t, c1, c2],
                self.next.car_order_in_train(t, c1, c2)
                == And(
                    self.car_order_in_train(t, c1, c2),
                    self.next.car_in_train(c1, t),
                    self.next.car_in_train(c2, t),
                ),
            ),
            self.train_in_yard.unchanged(),
        )

    @transition
    def remove_train(self, train: Train) -> BoolRef:
        # a train with a single car is removed from the yard
        c = Car("c")
        c0 = Car("c0")
        return And(
            self.train_in_yard(train),
            Exists(
                c0,
                And(
                    self.car_in_train(c0, train),
                    ForAll(c, Implies(self.car_in_train(c, train), c == c0)),
                ),
            ),
            self.train_in_yard.update({(train,): false}),
            self.car_in_train.unchanged(),
        )


class ShuntingYardProperty(Prop[ShuntingYard]):
    def prop(self) -> BoolRef:
        train = Train("train")
        return ForAll(train, Not(self.sys.train_in_yard(train)))


class ShuntingYardProof(Proof[ShuntingYard], prop=ShuntingYardProperty):

    def rank(self) -> Rank:
        return BinRank(true)
