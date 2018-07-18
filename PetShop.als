sig abstract Animal {

}

sig AnimalPequeno extends Animal {

}

sig AnimalMedio extends Animal {

}

sig AnimalGrande extends Animal {

}

sig Pessoa {
    adocoes: set Animal
}

fact Nome {
    all p: Pessoa | some p.adocoes
}
