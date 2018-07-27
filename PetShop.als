module PetShop

// Objeto que representa um animal, que possui um acessorio
abstract sig Animal {
    acessorio: one Acessorio
}

// Animal pode ser do tipo Pequeno, Médio ou Grande
sig AnimalPequeno, AnimalMedio, AnimalGrande extends Animal{}

// Objeto que representa o acessorio que acompanha cada animal
abstract sig Acessorio{}

// Os acessorios podem ser tanto uma gaiola(Para os tipos Pequeno e Médio) quanto uma
// racao (para os do tipo Grande)
sig gaiola, racao extends Acessorio{}

// Objeto que representa uma pessoa que adotou algum animal 
sig Pessoa {
    adocoes: some Animal
}

-- Fatos --

fact RegrasAnimaisEAcessorios {
    
	all a: Animal | lone dono[a]
	all ac: Acessorio | umAnimalPorAcessorio[ac]
	all a: Animal | (isAnimalMedio[a] || isAnimalPequeno[a]) => acessorioDoAnimal[a] in gaiola
	all a: Animal | (isAnimalGrande[a]) => acessorioDoAnimal[a] in racao

}

fact RegrasDasDoacoes{	

	all p: Pessoa | maxAnimais[p]
	all p: Pessoa | (#animaisDasAdocoes[p] >= 1) => peloMenosUmPequeno[p]
	all p: Pessoa | (#animaisDasAdocoes[p]  = 3) => not todosPequenos[p]	
	all p: Pessoa | (#animaisDasAdocoes[p] = 3) => not umDeCada[p]
	all p: Pessoa | apenasUmGrande[p]

}

-- Funcoes --

// Retorna o respectivo acessorio do animal
fun acessorioDoAnimal[a: Animal]: set Acessorio{
    a.acessorio
}

// Retorna os animais adotados de uma pessoa
fun animaisDasAdocoes[p:Pessoa]: set Animal {
    p.adocoes
}

// Retorna o respectivo dono do animal
fun dono[a: Animal]: set Pessoa {
    a.~adocoes
}

-- Predicados --

// Pode haver apenas um animal grande por adoção
pred apenasUmGrande[p: Pessoa]{
  lone g : AnimalGrande | g in p.adocoes

}

// Tem que haver pelo menos um animal Pequeno em todas as adoções
pred peloMenosUmPequeno[p: Pessoa]{
	some pe : AnimalPequeno | pe in p.adocoes 

} 

// NEG : Em uma adoção de 3 animais, todos os animais sao pequenos
pred todosPequenos[p:Pessoa]{
    	all a : p.adocoes | a in AnimalPequeno 
}

// NEG: Existe uma adoção onde se encontram todos os tipos
pred umDeCada[p:Pessoa]{
    some a : animaisDasAdocoes[p] | a in AnimalPequeno && some a : animaisDasAdocoes[p] | a in AnimalMedio &&  some a : animaisDasAdocoes[p]| a in AnimalGrande	
}

//  Todo acessorio esta ligado a um animal
pred umAnimalPorAcessorio[ac: Acessorio]{
    one acessorio.ac
}

// A quantidade maxima de Animais por adocao é 3
pred maxAnimais[p:Pessoa]{
    #p.adocoes <= 3
}

// Animal é do tipo Pequeno
pred isAnimalPequeno[a: Animal]{
    a in AnimalPequeno
}

// Animal é do tipo Medio
pred isAnimalMedio[a: Animal]{
   a in AnimalMedio
}

// Animal é do tipo Grande
pred isAnimalGrande[a: Animal]{
    a in AnimalGrande
}


--------- Run -----------

pred show[]{}

run show for 10


--------------------------TESTES-------------------------------

// não pode ter adoção com mais de 3 animais
assert max3PorPessoa{
	all p: Pessoa | not #animaisDasAdocoes[p] > 3
}

check max3PorPessoa for 10

// não pode ter adoção sem nenhum animal pequeno
assert peloMenosUmAnimalPequeno{
	 all p: Pessoa | some a: animaisDasAdocoes[p] | isAnimalPequeno[a]
}

check peloMenosUmAnimalPequeno for 10

// nenhum animal Pequeno ou Medio podem ter ração
assert nenhumAnimalPequenoComRacao{
	all a: Animal | (isAnimalPequeno[a]) => not a.acessorio in racao
}

check nenhumAnimalPequenoComRacao for 10

// nenhum animal Grande pode ter gaiola
assert nenhumAnimalGrandeComGaiola{
	all a: Animal | (isAnimalGrande[a]) => not a.acessorio in gaiola
}

check nenhumAnimalGrandeComGaiola for 10

// nenhum animal pode ter mais de um dono
assert animalComMaisDeUmDono{
	all a: Animal | not  #dono[a] > 1
}

check animalComMaisDeUmDono for 10

// nenhuma pessoa pode ter 0 animais
assert pessoaSemAnimal{
	all p: Pessoa | not #animaisDasAdocoes[p] = 0
}

check pessoaSemAnimal for 10

// nenhuma adoção de 3 animais com todos sendo animais pequenos
assert todosPequenos{
	all p: Pessoa | (#animaisDasAdocoes[p]  = 3) => not todosPequenos[p]
}

check todosPequenos for 10

// As adoções podem ter no maximo um Grande
assert somenteUmGrande{
	all p: Pessoa | apenasUmGrande[p]
}

check somenteUmGrande for 10

// Cada animal tem seu respectivo Acessorio
assert maisDeUmAnimalPorAcessorio{
	all ac: Acessorio | not #acessorio.ac > 1

}

check maisDeUmAnimalPorAcessorio for 10

// Nenhum animal pode ter mais de um dono
assert maisDeUmDonoPorAnimal{
	all a: Animal | not #adocoes.a > 1	

}

check maisDeUmDonoPorAnimal for 10





