#include "regexp.h"
#include <string.h>


char* avancer(char * expr){
    char* expr2=malloc(sizeof(strlen(expr))-1);

    for(int i=0;i<strlen(expr);i++){

        expr2[i]=expr[i+1];

    }

    return expr2;
}


int erreur (int code) {
    if (code==1)  fprintf(stderr,"pas de symbole '#' de fin d'expr, mot NON RECONNU\n");
    if (code==2)  fprintf(stderr,"Caractère inconnu dans l'expression régulière.\n");
    if (code==3)  fprintf(stderr,"Plus de mémoire, malloc a échoué.\n");
    if (code==21) fprintf(stderr,"manque une parenthèse fermante\n");
    if (code==22) fprintf(stderr,"manque une parenthèse ouvrante\n");
    if (code==23) fprintf(stderr,"mot RECONNU\n");
    if (code==24) fprintf(stderr,"mot NON RECONNU\n");
    if (code==25) fprintf(stderr,"fin du mot\n");
    if (code==34) fprintf(stderr,"Mauvais Parenthèsage\n");
    return(code);
}

int verif_expr(char *expr){
    int taille = strlen(expr);
    PILE p = nouvelle_pile(taille*2);

    /*on verifie ici si il y a bien un symbole #
     * qui indique une fin de mot
     * si il n'y en a pas : expr non reconnu
     * sinon on continue la verification*/
    int indice = 0;
    int niveau = 0;
    while (expr[indice] != '\0') {
        if (expr[indice] == '#') niveau++;
        indice++;
    }
    if (niveau == 0){erreur(1); exit(0);}

    /*on verifie maintenant le parenthèsage*/
    while ( (*expr != '(') ) {//si la 1ère parenthèse n'est pas une ouvrante
        if (*expr == '\0'){//   alors le parenthèsage est faux
            erreur(22);
            erreur(24);
            return 0;
        }
        expr++;
    }

    /*quand on tombe sur une PARO on empile,
     * quand on tombe sur une PARF on dépile
     *
     * si on tombe sur une PARF
     * (au milieu de la chaine expr car déja verif pour 1ere parenthèse)
     * alors que la pile est vide
     * c'est que c'est mal parenthèsée alors on retourne 0
     */
    while(expr[0]!='\0'){
        if(expr[0]=='(') p=empiler(p,PARO);
        if(expr[0]==')') depiler(&p);
        expr=avancer(expr);
        if(expr[0]==')' && est_vide(p)) return 0;
        if(expr[0]=='(') p=empiler(p,PARO);
        if(expr[0]==')') depiler(&p);
        expr=avancer(expr);
    }

    /*si on arrive jusqu'ici et que la pile est vide
     * alors c'est bien parenthèsé
     * on retourne 1
     */
    if (est_vide(p)) return 1;
    else {erreur(34); erreur(24); return 0;}
}

ADERIV nouvel_arbre(STATE s, char c){
    ADERIV a = malloc(sizeof(struct aderiv));
    if(!a) {erreur(3); exit(5);}
    a->s = s;
    a->caractere = c;
    a->fils[0] = NULL;
    a->fils[1] = NULL;
    a->fils[2] = NULL;
    return a;
}

void liberer_arbre(ADERIV a){
    if(a){
        for(int i = 0; i < 3; i++) liberer_arbre(a->fils[i]);
        free(a);
    }
}


int indice_char(char c){//retourne l'indice correspondant au caractère dans le tableau des états
    switch(c){
        case '+': return 0;
        case '.': return 1;
        case '*': return 2;
        case '(': return 3;
        case ')': return 4;
        case '#': return 6;
        default:
            if( c >= 'a' && c <= 'z') return 5;
            erreur(2);
            exit(3);
    }
}

REGEXP init_e(char *expr){
    REGEXP e = malloc(sizeof(struct regexp));
    if(!e) {erreur(3); exit(5);}
    e->car   = expr[0];
    e->arite = 0;
    e->filsg = NULL;
    e->filsd = NULL;
    return e;
}

STATE quel_etat(char c){
    switch(c){
        case '+': return PLUS;
        case '.': return POINT;
        case '*': return ETOILE;
        case '(': return PARO;
        case ')': return PARF;
        case '#': return CAR;
        default:
            if( c >= 'a' && c <= 'z') return CAR;
            erreur(2);
            exit(3);
    }
}

ADERIV construire_arbre_derivation(char *expr){
    STATELISTE table[7][7] = {//cette table représente la table des transitions de l'énoncé
            {{-1},{-1},{-1},{2,{A,B}},{-1},{2,{A,B}},{-1}}, // transition quand le STATE S est lu
            {{-1},{-1},{-1},{2,{C,D}},{-1},{2,{C,D}},{-1}},//STATE A
            {{3,{PLUS,A,B}},{-1},{-1},{-1},{0},{-1},{1,{CAR}}},//STATE B
            {{-1},{-1},{-1},{2,{E,F}},{-1},{2,{E,F}},{-1}},//STATE C
            {{0},{3,{POINT,C,D}},{-1},{-1},{0},{-1},{0}},//STATE D
            {{0},{0},{0},{3,{PARO,S,PARF}},{-1},{1,{CAR}},{-1}},//STATE E
            {{0},{0},{2,{ETOILE,F}},{-1},{0},{-1},{0}}//STATE F
    };
    //Une STATELISTE de taille 0 correspond à une règle dont la production est epsilon.
    //Une STATELISTE de taille -1 correspond à une erreur (expression rejetée)
    int taille = strlen(expr);
    PILE p = nouvelle_pile(taille*2);//pile des etats
    p=empiler(p,S);//on initialise la pile avec S
    ADERIV a = nouvel_arbre(p.contenu[p.sommet-1],0);//on inisialise l'arbre avec le sommet de la pile ; S
    int decalage=0; //decalage pour affichage de l'arbre
    int rang; //indice de l'expr
    STATE test;//etat utilisé pour tester la correspondance avec le caractère courant de l'expr

    while(expr[0]!='\0') {   //tant qu'on est pas a la fin de la chaine
        rang = indice_char(expr[0]);
        decalage++;
        a = nouvel_arbre(p.contenu[p.sommet - 1], 0);//on crée un nouveau noeud avec le symbole du sommet de la pile

        /*règle d'arret*/
        if (est_vide(p) && expr[0] != '\0') {
            erreur(24);
            exit(0);
        }

        if (a->s <= 6) { // si sommet de la pile est un non terminal
            if (table[a->s][rang].taille != 0 &&
                table[a->s][rang].taille != -1) {//si il y a une regle pour le symbole et caractère courant
                depiler(&p); //on dépile
                for (int j = table[a->s][rang].taille - 1; j >= 0; j--) {
                    p = empiler(p, table[a->s][rang].liste[j]);// on empile les symboles
                    a->fils[j] = nouvel_arbre(table[a->s][rang].liste[j], 0);
                }
                affiche_aderiv(a, decalage);
            } else { depiler(&p); }
        }
        else { //  si sommet de la pile est un terminal
            test = quel_etat(expr[0]);
            if (a->s == test) {//si le sommet de la pile est égal au caractère courant
                a->caractere = expr[0];
                depiler(&p);//on depile le c
                expr = avancer(expr);//on passe au caractère suivant de l'expr voir fct avancer
            } else {
                erreur(24);
                exit(0);
            }
        }
    }
    erreur(23);
    return a;
}

void affiche_aderiv(ADERIV a, int space){//rendre joli
    //affiche les fils de gauche à droite
    if(a){
        affiche_aderiv(a->fils[2], space + 1);
        affiche_aderiv(a->fils[1], space + 1);
        for(int i = 0; i < space; i++) printf("   ");
        affiche_state(a->s);
        if(a->s == CAR) printf(" : %c",a->caractere);
        printf("\n");
        affiche_aderiv(a->fils[0], space + 1);
    }
}



