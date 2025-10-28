"""
This example is about how to use the streaming interface to start a chat request
and handle chat events
"""

import os
# Our official coze sdk for Python [cozepy](https://github.com/coze-dev/coze-py)
from cozepy import COZE_CN_BASE_URL

# Get an access_token through personal access token or oauth.
coze_api_token = 'cztei_lErA4qC5JTCYOf0WAlFHbZWhOV5iBRH66HfN16R5gf0F2A1GBq1AH6LIPGHYLyxFf'
# The default access is api.coze.com, but if you need to access api.coze.cn,
# please use base_url to configure the api endpoint to access
coze_api_base = COZE_CN_BASE_URL

from cozepy import Coze, TokenAuth, Message, ChatStatus, MessageContentType, ChatEventType  # noqa

# Init the Coze client through the access_token.
coze = Coze(auth=TokenAuth(token=coze_api_token), base_url=coze_api_base)

# Create a bot instance in Coze, copy the last number from the web link as the bot's ID.
bot_id = '7564697855882559507'
# The user id identifies the identity of a user. Developers can use a custom business ID
# or a random string.
user_id = '123456789'

# Call the coze.chat.stream method to create a chat. The create method is a streaming
# chat and will return a Chat Iterator. Developers should iterate the iterator to get
# chat event and handle them.

prompt="你是一个擅长使用Litex格式的数学家。你将会收到若干数学问题的自然语言描述。你将会按照示例中的格式，将nl_problem中描述的问题转换成litex格式的命题陈述，并生成完整的、可执行的证明脚本。请严格按照示例进行输出，并不要写任何注释或多余的文字。\n 示例输入：nl_problem: Three cubes have edges of lengths 4,5 and 6 .\n\nThe average (mean) of their volumes is\n(A) 120\n(B) 125\n(C) 1125\n(D) 261\n(E) 135\n\n![](https://cdn.mathpix.com/cropped/2024_04_20_ac36362783317e0251fdg-104.jpg?height=249&width=379&top_left_y=1220&top_left_x=1293) 示例输出：    formal_statement: forall e1, e2, e3, v1, v2, v3, partial_sum, total_sum, avg N_pos:\n        e1 = 4\n        e2 = 5\n        e3 = 6\n        v1 = e1 ^ 3\n        v2 = e2 ^ 3\n        v3 = e3 ^ 3\n        partial_sum = v1 + v2\n        total_sum = partial_sum + v3\n        avg = total_sum / 3\n        =>:\n            avg = 135, formal_code: claim:\n    forall e1, e2, e3, v1, v2, v3, partial_sum, total_sum, avg N_pos:\n        e1 = 4\n        e2 = 5\n        e3 = 6\n        v1 = e1 ^ 3\n        v2 = e2 ^ 3\n        v3 = e3 ^ 3\n        partial_sum = v1 + v2\n        total_sum = partial_sum + v3\n        avg = total_sum / 3\n        =>:\n            avg = 135\n    prove:\n        v1 = 4 ^ 3\n        v1 = 64\n\n        v2 = 5 ^ 3\n        v2 = 125\n\n        v3 = 6 ^ 3\n        v3 = 216\n\n        partial_sum = v1 + v2\n        partial_sum = 64 + 125\n        partial_sum = 189\n\n        total_sum = partial_sum + v3\n        total_sum = 189 + 216\n        total_sum = 405\n\n        avg = total_sum / 3\n        avg = 405 / 3\n        avg = 135}"
for event in coze.chat.stream(
    bot_id=bot_id,
    user_id=user_id,
    additional_messages=[
        Message.build_user_question_text("nl_problem:Prove rigorously using syllogism that the function $y= \\frac {2^{x}-1}{2^{x}+1}$ is an odd function."+prompt),
    ],
):
    if event.event == ChatEventType.CONVERSATION_MESSAGE_DELTA:
        print(event.message.content, end="", flush=True)

    if event.event == ChatEventType.CONVERSATION_CHAT_COMPLETED:
        print()
        print("token usage:", event.chat.usage.token_count)