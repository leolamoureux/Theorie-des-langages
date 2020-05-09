#include "pile.h"


struct aderiv{
    STATE s;// symbole de la grammaire contenu dans le sommet
    char caractere;//si s est CAR, contient la valeur du caractère, 0 sinon
    struct aderiv *fils[3];//un noeud a au plus trois enfants (cas du +, du * et de ())
    //si le noeud a un fils c'est fils[0], deux fils fils[0] et fils[1] ...
};

typedef struct aderiv *ADERIV;//arbre de dérivation

typedef struct{ //liste d'états pour la table de transition
	int taille;//au plus trois symboles dans la liste
	STATE liste[3];
}STATELISTE;

ADERIV nouvel_arbre(STATE s, char c);//mettre la valeur du caractère pour c si l'état est CAR, 0 sinon
void affiche_aderiv(ADERIV a, int space);//affiche un arbre de dérivation
void liberer_arbre(ADERIV a);//libère la mémoire
ADERIV construire_arbre_derivation(char *expr);//A IMPLEMENTER
char* avancer(char * expr);
int verif_expr(char *expr);// renvoie 1 si le parenthèsage est cohérent, 0 sinon
STATE quel_etat(char c); //renvoie l'etat correspondant a un char contenu dans l'expr si il est terminal

//structure de donnée pour l'arbre de l'expression régulière obtenu à partir du parse tree

struct regexp{
    char car;// le caractère contenant la valeur du sommet
    char arite;// 0 pour les feuilles (les lettres), 1 pour les sommets unaires (l'opérateur *), 2 pour les sommets
    //binaires (les opérateurs +, .)
    struct regexp *filsg;
    struct regexp *filsd;
};

typedef struct regexp *REGEXP;

