# Minhocaos: servidor do jogo

O servidor roda a partida inteira. Cada jogador só manda a direção e se está acelerando, e o servidor decide quem comeu, quem cortou e quem bateu. Todo mundo vê o mesmo resultado.

Não precisa instalar nada além do Node 18 ou mais novo. Não tem dependências.

```
node server.js
```

Abra http://localhost:8080 no navegador.

## O que tem aqui

| Arquivo | Para que serve |
|---|---|
| `server.js` | Servidor: simulação, salas e WebSocket |
| `public/index.html` | A página do jogo, servida em `/` |
| `package.json` | Comando de início (`npm start`) |
| `squarecloud.app` | Configuração para a Square Cloud |
| `fly.toml` + `Dockerfile` | Configuração para o Fly.io (servidor em São Paulo) |
| `render.yaml` | Configuração para o Render |

Endereços úteis depois de publicar:
- `/health` responde `ok`. Use para checar se está no ar.
- `/stats` mostra as salas abertas e quantas pessoas há em cada uma.

## Opção A: Square Cloud (painel em português, enviar um .zip)

1. Crie a conta em squarecloud.app e assine o plano Hobby.
2. Se o nome `minhocaos` já estiver em uso, troque `SUBDOMAIN=minhocaos` no arquivo `squarecloud.app`.
3. No painel, clique em **Upload** e envie o `minhocaos-servidor.zip`.
4. O jogo fica em `https://minhocaos.squareweb.app` (ou o subdomínio que você escolheu).

## Opção B: Fly.io (menor atraso para quem joga no Brasil)

1. Crie a conta em fly.io. Eles pedem cartão.
2. Instale a ferramenta `flyctl` (instruções em fly.io/docs/flyctl/install).
3. Descompacte o zip, abra o terminal na pasta e rode:
   ```
   fly auth login
   fly launch --copy-config --ha=false --name minhocaos --region gru --now
   ```
   Se o nome `minhocaos` estiver ocupado, troque por outro (ex.: `minhocaos-g`) no comando e rode de novo. Se perguntar se quer ajustar as configurações, responda que não.

   Importante: o jogo precisa de **uma máquina só**. Com duas, cada amigo pode cair numa partida diferente. O `--ha=false` garante isso. Para conferir, rode `fly scale count 1`.
4. O jogo fica em `https://minhocaos.fly.dev` (ou o nome que você escolheu).

A máquina desliga sozinha quando ninguém está jogando e liga em 1 a 2 segundos quando alguém entra. Assim o custo fica baixo.

## Opção C: Render (grátis, servidor nos EUA)

1. Crie uma conta no GitHub. Crie um repositório e envie estes arquivos pelo botão **Add file > Upload files**.
2. Em render.com, crie a conta com o GitHub e clique em **New > Blueprint**. Escolha o repositório. O `render.yaml` já configura tudo.
3. No plano grátis o servidor dorme depois de 15 minutos sem ninguém. O primeiro a entrar espera cerca de 1 minuto.

## Ligar na página da Atomicat

Depois de publicar, a página nativeswipe.com.br/minhocaos só precisa mostrar o endereço do servidor em tela cheia. Mande o endereço e eu faço essa troca.

## Testes (só para desenvolvimento)

- `MINHOCAOS_DEV=1` libera comandos de teste: dar um poder ou mudar o tamanho.
- `MINHOCAOS_LAG=140` simula 140 ms de atraso de rede.
- Abra a página com `?debug` para expor o estado em `window.__mh`.
