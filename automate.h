#include <stdlib.h>
#include <stdio.h>
#include <string.h>

struct transition {
    char car;//caractère étiquetant la transition. -1 si c'est une epsilon transition
    int arr;//état d'arrivée de la transition
    struct transition *suiv;
};

typedef struct transition *TRANSITION ;

typedef struct{
    int sigma; // Le nombre de lettre de l'alphabet, les lettres de l'alphabet étant les minuscules. Ce qui limite donc à 26
    int Q; // Le nombre d'états qui sont numérotés de 0 à Q-1. 0 étant l'état initial
    int *F; // Un tableau monodimensionnel de taille Q qui indique pour chaque état s'il est final ou non
    TRANSITION *T; //Un tableau de taille Q donnant pour chaque état la liste des transitions depuis cet état
}AUTOMATE;

struct etatnd{
	int *ensemble_etat;//un etat non déterministe est un ensemble d'état
	TRANSITION T;//liste des transitions pour cet état
	int rang;//rang dans la liste de l'élément
	struct etatnd *suiv;
};

typedef struct etatnd *ETATND;

////////////////////Liste des fonctions de manipulation d'automates fournies ////////////////////////////////////


TRANSITION copie_liste(TRANSITION T, int decalage, int conserve_epsilon);//copie une liste de transitions, en ajoutant décalage au numero de l'état d'arrivée 
//si conserve_epsilon == 0, ne conserve pas les epsilon transitions
AUTOMATE automate_creer (int Q); // Création d'un automate de taille Q, sans états finaux et sans transitions
AUTOMATE automate_copier(AUTOMATE A, int conserve_epsilon);//créé une copie fraiche de l'automate A
//si conserve_epsilon == 0, ne conserve pas les epsilon transitions

void automate_ajouter_transition (AUTOMATE A, int dep, char car, int arr); // Ajoute la transition (dep,car,arr) à l'automate (ne fait rien si elle existe)
//void automate_supprimer_transition (AUTOMATE A, int dep, char car, int arr); // Ne fait rien si elle n'existe pas
void automate_ajouter_final (AUTOMATE A, int q); //ajoute l'état q aux états finaux
void automate_supprimer_final (AUTOMATE A, int q); //supprime l'état q des états finaux
void automate_liberer_memoire(AUTOMATE A);// libère la mémoire allouée dynamiquement pour l'automate
void automate_ecrire (AUTOMATE A, char* nomfic); // Ecrit un automate dans un fichier sous la forme :
/*
Q F T
F_1 F_2 F_3 ... F_F
dep_1 car_1 arr_1
dep_2 car_2 arr_2
...
dep_T car_T arr_T
Q : nombre d'états
F : nombre d'états finaux
T : nombres de transitions
F_i : les numéros des états finaux
dep_j car_j arr_J : une transition
*/
AUTOMATE automate_lire (char* nomfic); // Lit un automate depuis un fichier sous la forme précédente
AUTOMATE automate_supprimer_epsilon(AUTOMATE A);//renvoie un automate sans epsilon transition qui reconnait le 
// même langage que A

//////////////////////////// Fonction à programmer vous même /////////////////////////////////////////////////

AUTOMATE automate_une_lettre(char car);//renvoie l'automate qui reconnait le mot constitué de la lettre car ou epsilon si car = -1
AUTOMATE automate_epsilon();//renvoie l'automate qui reconnait le mot epsilon
AUTOMATE automate_concatenation(AUTOMATE A, AUTOMATE B);//renvoie un automate qui reconnaît la concaténation des
//langages reconnus par A et B
AUTOMATE automate_disjonction(AUTOMATE A, AUTOMATE B);//renvoie un automate qui reconnaît la disjonction des
//langages reconnus par A et B
AUTOMATE automate_etoile(AUTOMATE A);//renvoie un automate qui reconnaît l'étoile de Kleene du langage du langage reconnu par A
AUTOMATE automate_determiniser(AUTOMATE A);//renvoie un automate déterministe qui reconnait le même langage que A
