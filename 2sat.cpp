#include <iostream>
#include <vector>
#include <sstream>

using namespace std;

void print_entrada(const vector< vector<int> >& entrada)
{
    cout << " [entrada]"<< endl;
    for(unsigned i=0;i<entrada.size();i++)
    {
        cout << "  ";
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            cout << entrada[i][j] << "   ";
        }
        cout<<endl;
    }
    cout << " ---------"<< endl;
}

// array de clausulas unitarias encontado pelo find_cla_uni
vector<int> claus_uni_arr;

int find_cla_uni(const vector< vector<int> >& entrada)
{
    // achar a primeira clausula unitaria
    for(unsigned i=0;i<entrada.size();i++)
    {
        int atomo = 0;
        int cont = 0;
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            if(entrada[i][j] != 0)
            {
                atomo = entrada[i][j];
                cont++;
            }
        }

        if(cont == 1)
        {
            claus_uni_arr.push_back(atomo);
            return atomo;
        }
    }

    return 0;
}

void print_satisfazibility(bool res)
{
    if(res){ std::cout << "\n Resultado: [satisfazivel]\n\n";   }
    else   { std::cout << "\n Resultado: [insatisfazivel]\n\n"; exit(0); }
}

void simplifica(vector< vector<int> >& entrada)
{
    for(;;)
    {
        // Procurar primeira cláusula unitária
        int claus = find_cla_uni(entrada);
        if(claus == 0){ break; }

        for(unsigned i=0; i<entrada.size(); i++)
        {
            for(unsigned j=0; j<entrada[i].size(); j++)
            {
                // Deletar clausula unitária junto com a linha.
                if(entrada[i][j] == claus)
                {
                    entrada.erase(entrada.begin()+i);
                }

                // Substituir a negação da clausula unitaria por zero
                if(entrada[i][j] == claus * -1)
                {
                    //entrada[i].erase(entrada[i].begin()+j);
                    entrada[i][j] = 0;
                }
            }
        }
    }
}

int get_atom_p(const vector< vector<int> >& entrada)
{
    int p = 0;
    for(unsigned i=0; i<entrada.size(); i++)
    {
        for(unsigned j=0; j<entrada[i].size(); j++)
        {
            if(entrada[i][j] != 0)
            {
                if(p == 0)
                {
                    p = entrada[i][j];
                }
            }
            break;
        }
    }

    return p;
}

bool has_contradiction(const vector< vector<int> >& entrada)
{
    // Verificar se existe contradição
    for(unsigned i=0; i<entrada.size(); i++)
    {
        unsigned cont = 0;
        for(unsigned j=0; j<entrada[i].size(); j++)
        {
            if(entrada[i][j] == 0){ cont++; }
        }

        if(cont == entrada[i].size())
        {
            return true;
        }
    }

    return false;
}

bool struct_empty(const vector< vector<int> >& entrada)
{
    if(entrada.size() == 0) { return true; }
    return false;
}

vector< vector<int> > copy_entrada(const vector< vector<int> >& entrada)
{
    vector< vector<int> > entrada_cpy;

    for(unsigned i=0; i<entrada.size(); i++)
    {
        vector<int> buffer;
        for(unsigned j=0; j<entrada[i].size(); j++)
        {
            buffer.push_back(entrada[i][j]);
        }
        entrada_cpy.push_back(buffer);
    }

    return entrada_cpy;
}

bool twosat(vector< vector<int> >& entrada)
{
    // antes de tudo, verificar se há alguma clausula vazia na estrutura original.
    for(unsigned i=0; i<entrada.size(); i++)
    {
        if(entrada[i].size() == 0) { return false; }
    }

    simplifica(entrada);

    // Verificar se existe contradição
    bool res = has_contradiction(entrada);
    if(res){ return false; }

    // Verificar se estrutura esta completamente vazia
    res = struct_empty(entrada);
    if(res){ return true; }

    while(!has_contradiction(entrada) && !struct_empty(entrada))
    {
        // Guardar um backup da estrutura
        auto entrada_cpy = copy_entrada(entrada);

        // Escolher um p qualquer na estrutura
        int p = get_atom_p(entrada);

        // Colocar o p na estrutura e chamar o simplifica
        entrada.push_back(vector<int>{p});
        simplifica(entrada);

        // Verificar se deu contradição
        if(has_contradiction(entrada))
        {
            // Colocar -p na copia da estrutura e chamar o simplifica
            entrada_cpy.push_back(vector<int>{p * -1});
            entrada = copy_entrada(entrada_cpy);

            simplifica(entrada);
        }
    }

    // Verificar se deu contradição
    if(has_contradiction(entrada))
    {
        return false;
    } else
    {
        return true;
    }
}

void print_valoration(const std::vector< std::vector<std::string> >& entrada)
{
    // imprimir a formula
    for(unsigned i=0;i<entrada.size();i++)
    {
        std::cout << " (";
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            std::cout << entrada[i][j] << (j==entrada[i].size()-1 ? "" : "#");

        }
        std::cout << ") ";
        std::cout << (i==entrada.size()-1 ? "" : "&");
    }
    std::cout<<std::endl;
}

void show_valoration(const vector< vector<int> >& entrada)
{
    std::cout << " Valoração: \n";

    // transformar a estrutura em array de strings para representar o (-0)
    std::vector< std::vector<std::string> > entrada_str;
    for(unsigned i=0;i<entrada.size();i++)
    {
        std::vector<std::string> buffer;
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            std::stringstream ss;
            ss << entrada[i][j];
            std::string str = ss.str();
            buffer.push_back(str);
        }
        entrada_str.push_back(buffer);
    }

    print_valoration(entrada_str);

    // Substituir as clausulas unitarias por 1
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        for(unsigned j=0;j<entrada_str[i].size();j++)
        {
            bool is_unit_claus = false;
            for(unsigned k=0;k<claus_uni_arr.size();k++)
            {
                stringstream ss;
                ss << claus_uni_arr[k];

                if(entrada_str[i][j] == ss.str())
                {
                    is_unit_claus = true;
                }
            }
            if(is_unit_claus)
            {
                entrada_str[i][j] = "1";
            } else
            {
                entrada_str[i][j] = "0";
            }
        }
    }

    print_valoration(entrada_str);

    // Simplificação #1
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        int cont = 0;
        for(unsigned j=0;j<entrada_str[i].size();j++)
        {
            if(entrada_str[i][j] == "1"){ cont++ ; }
        }

        if(cont > 0)
        {
            entrada_str[i].clear();
            entrada_str[i].push_back("1");
        } else
        {
            entrada_str[i].clear();
            entrada_str[i].push_back("0");
        }
    }

    print_valoration(entrada_str);

    // Simplificação #2
    int cont = 0;
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        if(entrada_str[i][0] == "1")
        {
            cont++;
        }
    }

    bool res = ((unsigned)cont == entrada_str.size());
    entrada_str.clear();
    if(res)
    {
        entrada_str.push_back(vector<string>{"1"});
    } else
    {
        entrada_str.push_back(vector<string>{"99"});
    }

    print_valoration(entrada_str);

    cout<<endl;
}

std::vector< std::vector<int> > openfile(std::string path)
{
    FILE* file = fopen(path.c_str(), "r");
    std::stringstream file_content;

    puts("");
    int j = 0;
    while((j = fgetc(file)) != EOF)
    {
        file_content << (char)j;
    }

    fclose(file);

    std::vector< std::vector<int> > entrada;

    int val = 0;
    int c = 0;
    int sig = 1;
    std::vector<int> buffer;
    for(unsigned i=0;i<file_content.str().size();i++)
    {

        if(file_content.str()[i] == '-') { sig = -1; }
        if(isdigit(file_content.str()[i]))
        {
            do
            {
                c = file_content.str()[i];
                if(!isdigit(c)){ break; }
                else { val = val*10 + (c-48); }
                i++;
            }
            while(val>=0);
            //printf("%d ", (val * sig));
            buffer.push_back(val * sig);
            sig = 1;
        }

        if(file_content.str()[i] == '\n' || file_content.str()[i] == '\r'){
            //printf("\n");
            entrada.push_back(buffer);
            buffer.clear();
        }

        val = 0;
    }

    return entrada;
}



int main(int argc, char* argv[])
{
    if(argc != 2)
    {
        std::cout << " > ERRO - comando incorreto.\n";
        return 0;
    }
    system("clear");
    std::cout << endl;
    std::cout << " [arquivo] " << argv[1] << endl;
    std::cout << " [algorit] 2SAT\n";

    vector< vector<int> > entrada = openfile(argv[1]);
    auto entrada_cpy = copy_entrada(entrada);

    print_entrada(entrada);
    bool res = twosat(entrada);

    if(res) { print_satisfazibility(true);  }
    else    { print_satisfazibility(false); }

    show_valoration(entrada_cpy);

    return 0;
}
