package math;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

public class Prototype {

    private static int ord10pow2(int e) {
        // Constants suggested by Raffaello Giulietti
        long Q = 41;
        long C = 661_971_961_083L;
        return (int) ((C * e) >> Q) + 1;
    }

    private static class NumCQ {

        final int q;
        final BigInteger c;

        NumCQ(int q, BigInteger c) {
            this.q = q;
            this.c = c;
        }
    }

    static final int MIN_POW_5 = -292;

    // Floating point approximation of powers of 5 with 126-bit precision
    private static List<NumCQ> powers5 = new ArrayList<>();

    private static void p(int q, long ch, long cl) {
        assert ch >= 0 && cl >= 0;
        BigInteger c = BigInteger.valueOf(ch);
        c = c.shiftLeft(63).or(BigInteger.valueOf(cl));
        powers5.add(new NumCQ(q, c));
    }

    static {
        p(-804, 0x7fbbd8fe5f5e6e27L, 0x497a3a2704eec3dfL); // 5^-292
        p(-801, 0x4fd5679efb9b04d8L, 0x5dec645863153a6cL); // 5^-291
        p(-799, 0x63cac186ba81c60eL, 0x75677d6e7bda8906L); // 5^-290
        p(-797, 0x7cbd71e869223792L, 0x52c15cca1ad12b48L); // 5^-289
        p(-794, 0x4df6673141b562bbL, 0x53b8d9fe50c2bb0dL); // 5^-288
        p(-792, 0x617400fd9222bb6aL, 0x48a7107de4f369d0L); // 5^-287
        p(-790, 0x79d1013cf6ab6a45L, 0x1ad0d49d5e304444L); // 5^-286
        p(-787, 0x4c22a0c61a2b226bL, 0x20c284e25ade2aabL); // 5^-285
        p(-785, 0x5f2b48f7a0b5eb06L, 0x08f3261af195b555L); // 5^-284
        p(-783, 0x76f61b3588e365c7L, 0x4b2fefa1adfb22abL); // 5^-283
        p(-780, 0x4a59d101758e1f9cL, 0x5efdf5c50cbcf5abL); // 5^-282
        p(-778, 0x5cf04541d2f1a783L, 0x76bd73364fec3315L); // 5^-281
        p(-776, 0x742c569247ae1164L, 0x746cd003e3e73fdbL); // 5^-280
        p(-773, 0x489bb61b6ccccadfL, 0x08c402026e7087e9L); // 5^-279
        p(-771, 0x5ac2a3a247fffd96L, 0x6af502830a0ca9e3L); // 5^-278
        p(-769, 0x71734c8ad9fffcfcL, 0x45b24323cc8fd45cL); // 5^-277
        p(-766, 0x46e80fd6c83ffe1dL, 0x6b8f69f65fd9e4b9L); // 5^-276
        p(-764, 0x58a213cc7a4ffda5L, 0x26734473f7d05de8L); // 5^-275
        p(-762, 0x6eca98bf98e3fd0eL, 0x50101590f5c47561L); // 5^-274
        p(-759, 0x453e9f77bf8e7e29L, 0x120a0d7a999ac95dL); // 5^-273
        p(-757, 0x568e4755af721db3L, 0x368c90d940017bb4L); // 5^-272
        p(-755, 0x6c31d92b1b4ea520L, 0x242fb50f9001daa1L); // 5^-271
        p(-752, 0x439f27baf1112734L, 0x169dd129ba0128a5L); // 5^-270
        p(-750, 0x5486f1a9ad557101L, 0x1c454574288172ceL); // 5^-269
        p(-748, 0x69a8ae1418aacd41L, 0x435696d132a1cf81L); // 5^-268
        p(-745, 0x42096ccc8f6ac048L, 0x7a161e42bfa521b1L); // 5^-267
        p(-743, 0x528bc7ffb345705bL, 0x189ba5d36f8e6a1dL); // 5^-266
        p(-741, 0x672eb9ffa016cc71L, 0x7ec28f484b7204a4L); // 5^-265
        p(-738, 0x407d343fc40e3fc7L, 0x1f39998d2f2742e7L); // 5^-264
        p(-736, 0x509c814fb511cfb9L, 0x0707fff07af113a1L); // 5^-263
        p(-734, 0x64c3a1a3a25643a7L, 0x28c9ffec99ad5889L); // 5^-262
        p(-732, 0x7df48a0c8aebd491L, 0x12fc7fe7c018aeabL); // 5^-261
        p(-729, 0x4eb8d647d6d364daL, 0x5bddcff0d80f6d2bL); // 5^-260
        p(-727, 0x62670bd9cc883e11L, 0x32d543ed0e134875L); // 5^-259
        p(-725, 0x7b00ced03faa4d95L, 0x5f8a94e851981a93L); // 5^-258
        p(-722, 0x4ce0814227ca707dL, 0x4bb69d1132ff109cL); // 5^-257
        p(-720, 0x6018a192b1bd0c9cL, 0x7ea444557fbed4c3L); // 5^-256
        p(-718, 0x781ec9f75e2c4fc4L, 0x1e4d556adfae89f3L); // 5^-255
        p(-715, 0x4b133e3a9adbb1daL, 0x52f05562cbcd1638L); // 5^-254
        p(-713, 0x5dd80dc941929e51L, 0x27ac6abb7ec05bc6L); // 5^-253
        p(-711, 0x754e113b91f745e5L, 0x5197856a5e7072b8L); // 5^-252
        p(-708, 0x4950cac53b3a8bafL, 0x42feb3627b0647b3L); // 5^-251
        p(-706, 0x5ba4fd768a092e9bL, 0x33be603b19c7d99fL); // 5^-250
        p(-704, 0x728e3cd42c8b7a42L, 0x20adf849e039d007L); // 5^-249
        p(-701, 0x4798e6049bd72c69L, 0x346cbb2e2c242205L); // 5^-248
        p(-699, 0x597f1f85c2ccf783L, 0x6187e9f9b72d2a86L); // 5^-247
        p(-697, 0x6fdee76733803564L, 0x59e9e47824f87527L); // 5^-246
        p(-694, 0x45eb50a08030215eL, 0x78322ecb171b4939L); // 5^-245
        p(-692, 0x576624c8a03c29b6L, 0x563eba7ddce21b87L); // 5^-244
        p(-690, 0x6d3fadfac84b3424L, 0x2bce691d541aa268L); // 5^-243
        p(-687, 0x4447ccbcbd2f0096L, 0x5b6101b25490a581L); // 5^-242
        p(-685, 0x5559bfebec7ac0bcL, 0x3239421ee9b4cee1L); // 5^-241
        p(-683, 0x6ab02fe6e79970ebL, 0x3ec792a6a422029aL); // 5^-240
        p(-680, 0x42ae1df050bfe693L, 0x173cbba8269541a0L); // 5^-239
        p(-678, 0x5359a56c64efe037L, 0x7d0bea92303a9208L); // 5^-238
        p(-676, 0x68300ec77e2bd845L, 0x7c4ee536bc49368aL); // 5^-237
        p(-673, 0x411e093caedb672bL, 0x5db14f4235adc217L); // 5^-236
        p(-671, 0x51658b8bda9240f6L, 0x551da312c319329cL); // 5^-235
        p(-669, 0x65beee6ed136d134L, 0x2a650bd773df7f43L); // 5^-234
        p(-667, 0x7f2eaa0a85848581L, 0x34fe4ecd50d75f14L); // 5^-233
        p(-664, 0x4f7d2a469372d370L, 0x711ef14052869b6cL); // 5^-232
        p(-662, 0x635c74d8384f884dL, 0x0d66ad9067284247L); // 5^-231
        p(-660, 0x7c33920e46636a60L, 0x30c058f480f252d9L); // 5^-230
        p(-657, 0x4da03b48ebfe227cL, 0x1e783798d09773c8L); // 5^-229
        p(-655, 0x61084a1b26fdab1bL, 0x2616457f04bd50baL); // 5^-228
        p(-653, 0x794a5ca1f0bd15e2L, 0x0f9bd6dec5eca4e8L); // 5^-227
        p(-650, 0x4bce79e536762dadL, 0x29c1664b3bb3e711L); // 5^-226
        p(-648, 0x5ec2185e8413b918L, 0x5431bfde0aa0e0d5L); // 5^-225
        p(-646, 0x76729e762518a75eL, 0x693e2fd58d49190bL); // 5^-224
        p(-643, 0x4a07a309d72f689bL, 0x21c6dde5784dafa7L); // 5^-223
        p(-641, 0x5c898bcc4cfb42c2L, 0x0a38955ed6611b90L); // 5^-222
        p(-639, 0x73abeebf603a1372L, 0x4cc6bab68bf96274L); // 5^-221
        p(-636, 0x484b75379c244c27L, 0x4ffc34b2177bdd89L); // 5^-220
        p(-634, 0x5a5e5285832d5f31L, 0x43fb41de9d5ad4ebL); // 5^-219
        p(-632, 0x70f5e726e3f8b6fdL, 0x74fa125644b18a26L); // 5^-218
        p(-629, 0x4699b0784e7b725eL, 0x591c4b75eaeef658L); // 5^-217
        p(-627, 0x58401c96621a4ef6L, 0x2f635e5365aab3edL); // 5^-216
        p(-625, 0x6e5023bbfaa0e2b3L, 0x7b3c35e83f1560e9L); // 5^-215
        p(-622, 0x44f216557ca48db0L, 0x3d05a1b1276d5c92L); // 5^-214
        p(-620, 0x562e9beadbcdb11cL, 0x4c470a1d7148b3b6L); // 5^-213
        p(-618, 0x6bba42e592c11d63L, 0x5f58cca4cd9ae0a3L); // 5^-212
        p(-615, 0x435469cf7bb8b25eL, 0x2b977fe70080cc66L); // 5^-211
        p(-613, 0x542984435aa6def5L, 0x767d5fe0c0a0ff80L); // 5^-210
        p(-611, 0x6933e554315096b3L, 0x341cb7d8f0c93f5fL); // 5^-209
        p(-608, 0x41c06f549ed25e30L, 0x1091f2e7967dc79cL); // 5^-208
        p(-606, 0x52308b29c686f5bcL, 0x14b66fa17c1d3983L); // 5^-207
        p(-604, 0x66bcadf43828b32bL, 0x19e40b89db2487e3L); // 5^-206
        p(-601, 0x4035ecb8a3196ffbL, 0x002e873628f6d4eeL); // 5^-205
        p(-599, 0x504367e6cbdfcbf9L, 0x603a2903b3348a2aL); // 5^-204
        p(-597, 0x645441e07ed7bef8L, 0x1848b344a001acb4L); // 5^-203
        p(-595, 0x7d6952589e8daeb6L, 0x1e5ae015c80217e1L); // 5^-202
        p(-592, 0x4e61d37763188d31L, 0x72f8cc0d9d014eedL); // 5^-201
        p(-590, 0x61fa48553bdeb07eL, 0x2fb6ff110441a2a8L); // 5^-200
        p(-588, 0x7a78da6a8ad65c9dL, 0x7ba4bed545520b52L); // 5^-199
        p(-585, 0x4c8b888296c5f9e2L, 0x5d46f7454b534713L); // 5^-198
        p(-583, 0x5fae6aa33c77785bL, 0x3498b5169e2818d8L); // 5^-197
        p(-581, 0x779a054c0b955672L, 0x21bee25c45b21f0eL); // 5^-196
        p(-578, 0x4ac0434f873d5607L, 0x35174d79ab8f5369L); // 5^-195
        p(-576, 0x5d705423690cab89L, 0x225d20d816732843L); // 5^-194
        p(-574, 0x74cc692c434fd66bL, 0x4af4690e1c0ff253L); // 5^-193
        p(-571, 0x48ffc1bbaa11e603L, 0x1ed8c1a8d189f774L); // 5^-192
        p(-569, 0x5b3fb22a94965f84L, 0x068ef21305ec7551L); // 5^-191
        p(-567, 0x720f9eb539bbf765L, 0x0832ae97c76792a5L); // 5^-190
        p(-564, 0x4749c33144157a9fL, 0x151fad1edca0bba8L); // 5^-189
        p(-562, 0x591c33fd951ad946L, 0x7a67986693c8ea91L); // 5^-188
        p(-560, 0x6f6340fcfa618f98L, 0x59017e8038bb2536L); // 5^-187
        p(-557, 0x459e089e1c7cf9bfL, 0x37a0ef102374f742L); // 5^-186
        p(-555, 0x57058ac5a39c382fL, 0x25892ad42c523512L); // 5^-185
        p(-553, 0x6cc6ed770c83463bL, 0x0eeb75893766c256L); // 5^-184
        p(-550, 0x43fc546a67d20be4L, 0x79532975c2a03976L); // 5^-183
        p(-548, 0x54fb698501c68edeL, 0x17a7f3d3334847d4L); // 5^-182
        p(-546, 0x6a3a43e642383295L, 0x5d91f0c8001a59c8L); // 5^-181
        p(-543, 0x42646a6fe9631f9dL, 0x4a7b367d0010781dL); // 5^-180
        p(-541, 0x52fd850be3bbe784L, 0x7d1a041c40149625L); // 5^-179
        p(-539, 0x67bce64edcaae166L, 0x1c6085235019bbaeL); // 5^-178
        p(-536, 0x40d60ff149eaccdfL, 0x71bc53361210154dL); // 5^-177
        p(-534, 0x510b93ed9c658017L, 0x6e2b680396941aa0L); // 5^-176
        p(-532, 0x654e78e9037ee01dL, 0x69b642047c392148L); // 5^-175
        p(-530, 0x7ea21723445e9825L, 0x2423d2859b476999L); // 5^-174
        p(-527, 0x4f254e760abb1f17L, 0x26966393810ca200L); // 5^-173
        p(-525, 0x62eea2138d69e6ddL, 0x103bfc78614fca80L); // 5^-172
        p(-523, 0x7baa4a9870c46094L, 0x344afb9679a3bd20L); // 5^-171
        p(-520, 0x4d4a6e9f467abc5cL, 0x60aedd3e0c065634L); // 5^-170
        p(-518, 0x609d0a4718196b73L, 0x78da948d8f07ebc1L); // 5^-169
        p(-516, 0x78c44cd8de1fc650L, 0x771139b0f2c9e6b1L); // 5^-168
        p(-513, 0x4b7ab0078ad3dbf2L, 0x4a6ac40e97be302fL); // 5^-167
        p(-511, 0x5e595c096d88d2efL, 0x1d0575123dadbc3aL); // 5^-166
        p(-509, 0x75efb30bc8eb07abL, 0x0446d256cd192b49L); // 5^-165
        p(-506, 0x49b5cfe75d92e4caL, 0x72ac4376402fbb0eL); // 5^-164
        p(-504, 0x5c2343e134f79dfdL, 0x4f575453d03ba9d1L); // 5^-163
        p(-502, 0x732c14d98235857dL, 0x032d2968c44a9445L); // 5^-162
        p(-499, 0x47fb8d07f161736eL, 0x11fc39e17aae9cabL); // 5^-161
        p(-497, 0x59fa7049edb9d049L, 0x567b4859d95a43d6L); // 5^-160
        p(-495, 0x70790c5c6928445cL, 0x0c1a1a704fb0d4ccL); // 5^-159
        p(-492, 0x464ba7b9c1b92ab9L, 0x4790508631ce84ffL); // 5^-158
        p(-490, 0x57de91a832277567L, 0x797464a7be42263fL); // 5^-157
        p(-488, 0x6dd636123eb152c1L, 0x77d17dd1add2afcfL); // 5^-156
        p(-485, 0x44a5e1cb672ed3b9L, 0x1ae2eea30ca3ade1L); // 5^-155
        p(-483, 0x55cf5a3e40fa88a7L, 0x419baa4bcfcc995aL); // 5^-154
        p(-481, 0x6b4330cdd1392ad1L, 0x320294dec3bfbfb0L); // 5^-153
        p(-478, 0x4309fe80a2c3bac2L, 0x6f419d0b3a57d7ceL); // 5^-152
        p(-476, 0x53cc7e20cb74a973L, 0x4b12044e08edcdc2L); // 5^-151
        p(-474, 0x68bf9da8fe51d3d0L, 0x3dd685618b294132L); // 5^-150
        p(-471, 0x4177c2899ef32462L, 0x26a6135cf6f9c8bfL); // 5^-149
        p(-469, 0x51d5b32c06afed7aL, 0x704f983434b83aefL); // 5^-148
        p(-467, 0x664b1ff7085be8d9L, 0x4c637e4141e649abL); // 5^-147
        p(-465, 0x7fdde7f4ca72e30fL, 0x7f7c5dd1925fdc15L); // 5^-146
        p(-462, 0x4feab0f8fe87cde9L, 0x7fadbaa2fb7be98dL); // 5^-145
        p(-460, 0x63e55d373e29c164L, 0x3f99294bba5ae3f1L); // 5^-144
        p(-458, 0x7cdeb4850db431bdL, 0x4f7f739ea8f19cedL); // 5^-143
        p(-455, 0x4e0b30d328909f16L, 0x41afa84329970214L); // 5^-142
        p(-453, 0x618dfd07f2b4c6dcL, 0x121b9253f3fcc299L); // 5^-141
        p(-451, 0x79f17c49ef61f893L, 0x16a276e8f0fbf33fL); // 5^-140
        p(-448, 0x4c36edae359d3b5bL, 0x7e258a51969d7808L); // 5^-139
        p(-446, 0x5f44a919c3048a32L, 0x7daeece5fc44d609L); // 5^-138
        p(-444, 0x7715d36033c5acbfL, 0x5d1aa81f7b560b8cL); // 5^-137
        p(-441, 0x4a6da41c205b8bf7L, 0x6a30a913ad15c738L); // 5^-136
        p(-439, 0x5d090d2328726ef5L, 0x64bcd358985b3905L); // 5^-135
        p(-437, 0x744b506bf28f0ab3L, 0x1dec082ebe720746L); // 5^-134
        p(-434, 0x48af1243779966b0L, 0x02b3851d3707448cL); // 5^-133
        p(-432, 0x5adad6d4557fc05cL, 0x0360666484c915afL); // 5^-132
        p(-430, 0x71918c896adfb073L, 0x04387ffda5fb5b1bL); // 5^-131
        p(-427, 0x46faf7d5e2cbce47L, 0x72a34ffe87bd18f1L); // 5^-130
        p(-425, 0x58b9b5cb5b7ec1d9L, 0x6f4c23fe29ac5f2dL); // 5^-129
        p(-423, 0x6ee8233e325e7250L, 0x2b1f2cfdb41776f8L); // 5^-128
        p(-420, 0x45511606df7b0772L, 0x1af37c1e908eaa5bL); // 5^-127
        p(-418, 0x56a55b889759c94eL, 0x61b05b2634b254f2L); // 5^-126
        p(-416, 0x6c4eb26abd303ba2L, 0x3a1c71efc1deea2eL); // 5^-125
        p(-413, 0x43b12f82b63e2545L, 0x4451c735d92b525dL); // 5^-124
        p(-411, 0x549d7b6363cdae96L, 0x756639034f7626f4L); // 5^-123
        p(-409, 0x69c4da3c3cc11a3cL, 0x52bfc7442353b0b1L); // 5^-122
        p(-406, 0x421b0865a5f8b065L, 0x73b7dc8a96144e6fL); // 5^-121
        p(-404, 0x52a1ca7f0f76dc7fL, 0x30a5d3ad3b99620bL); // 5^-120
        p(-402, 0x674a3d1ed354939fL, 0x1ccf48988a7fba8dL); // 5^-119
        p(-399, 0x408e66334414dc43L, 0x42018d5f568fd498L); // 5^-118
        p(-397, 0x50b1ffc0151a1354L, 0x3281f0b72c33c9beL); // 5^-117
        p(-395, 0x64de7fb01a609829L, 0x3f226ce4f740bc2eL); // 5^-116
        p(-393, 0x7e161f9c20f8be33L, 0x6eeb081e3510eb39L); // 5^-115
        p(-390, 0x4ecdd3c1949b76e0L, 0x3552e512e12a9304L); // 5^-114
        p(-388, 0x628148b1f9c25498L, 0x42a79e57997537c5L); // 5^-113
        p(-386, 0x7b219ade7832e9beL, 0x535185ed7fd285b6L); // 5^-112
        p(-383, 0x4cf500cb0b1fd217L, 0x1412f3b46fe39392L); // 5^-111
        p(-381, 0x603240fdcde7c69cL, 0x7917b0a18bdc7876L); // 5^-110
        p(-379, 0x783ed13d4161b844L, 0x175d9cc9eed39694L); // 5^-109
        p(-376, 0x4b2742c648dd132aL, 0x4e9a81fe35443e1cL); // 5^-108
        p(-374, 0x5df11377db1457f5L, 0x2241227dc2954da3L); // 5^-107
        p(-372, 0x756d5855d1d96df2L, 0x4ad16b1d333aa10cL); // 5^-106
        p(-369, 0x49645735a327e4b7L, 0x4ec2e2f24004a4a8L); // 5^-105
        p(-367, 0x5bbd6d030bf1dde5L, 0x42739baed005cdd2L); // 5^-104
        p(-365, 0x72acc843ceee555eL, 0x7310829a84074146L); // 5^-103
        p(-362, 0x47abfd2a6154f55bL, 0x27ea51a0928488ccL); // 5^-102
        p(-360, 0x5996fc74f9aa32b2L, 0x11e4e608b725aaffL); // 5^-101
        p(-358, 0x6ffcbb923814bf5eL, 0x565e1f8ae4ef15beL); // 5^-100
        p(-355, 0x45fdf53b630cf79bL, 0x15fad3b6cf156d97L); // 5^-99
        p(-353, 0x577d728a3bd03581L, 0x7b7988a482dac8fdL); // 5^-98
        p(-351, 0x6d5ccf2ccac442e2L, 0x3a57eacda3917b3cL); // 5^-97
        p(-348, 0x445a017bfebaa9cdL, 0x4476f2c0863aed06L); // 5^-96
        p(-346, 0x557081dafe695440L, 0x7594af70a7c9a847L); // 5^-95
        p(-344, 0x6acca251be03a951L, 0x12f9db4cd1bc1258L); // 5^-94
        p(-341, 0x42bfe57316c249d2L, 0x5bdc291003158b77L); // 5^-93
        p(-339, 0x536fdecfdc72dc47L, 0x32d3335403daee55L); // 5^-92
        p(-337, 0x684bd683d38f9359L, 0x1f88002904d1a9eaL); // 5^-91
        p(-334, 0x412f66126439bc17L, 0x63b50019a3030a33L); // 5^-90
        p(-332, 0x517b3f96fd482b1dL, 0x5ca240200bc3ccbfL); // 5^-89
        p(-330, 0x65da0f7cbc9a35e5L, 0x13cad0280eb4bfefL); // 5^-88
        p(-328, 0x7f50935bebc0c35eL, 0x38bd84321261efebL); // 5^-87
        p(-325, 0x4f925c1973587a1bL, 0x0376729f4b7d35f3L); // 5^-86
        p(-323, 0x6376f31fd02e98a1L, 0x64540f471e5c836fL); // 5^-85
        p(-321, 0x7c54afe7c43a3ecaL, 0x1d691318e5f3a44bL); // 5^-84
        p(-318, 0x4db4edf0daa4673eL, 0x3261abef8fb846afL); // 5^-83
        p(-316, 0x6122296d114d810dL, 0x7efa16eb73a6585bL); // 5^-82
        p(-314, 0x796ab3c855a0e151L, 0x3eb89ca6508fee71L); // 5^-81
        p(-311, 0x4be2b05d35848cd2L, 0x773361e7f259f507L); // 5^-80
        p(-309, 0x5edb5c7482e5b007L, 0x55003a61eef07249L); // 5^-79
        p(-307, 0x76923391a39f1c09L, 0x4a4048fa6aac8edbL); // 5^-78
        p(-304, 0x4a1b603b06437185L, 0x7e682d9c82abd949L); // 5^-77
        p(-302, 0x5ca23849c7d44de7L, 0x3e023903a356cf9bL); // 5^-76
        p(-300, 0x73cac65c39c96161L, 0x2d82c7448c2c8382L); // 5^-75
        p(-297, 0x485ebbf9a41ddcdcL, 0x6c71bc8ad79bd231L); // 5^-74
        p(-295, 0x5a766af80d255414L, 0x078e2bad8d82c6bdL); // 5^-73
        p(-293, 0x711405b6106ea919L, 0x0971b698f0e3786dL); // 5^-72
        p(-290, 0x46ac8391ca4529afL, 0x55e7121f968e2b44L); // 5^-71
        p(-288, 0x5857a4763cd6741bL, 0x4b60d6a77c31b615L); // 5^-70
        p(-286, 0x6e6d8d93cc0c1122L, 0x3e390c515b3e239aL); // 5^-69
        p(-283, 0x4504787c5f878ab5L, 0x46e3a7b2d906d640L); // 5^-68
        p(-281, 0x5645969b77696d62L, 0x789c919f8f488bd0L); // 5^-67
        p(-279, 0x6bd6fc425543c8bbL, 0x56c3b607731aaec4L); // 5^-66
        p(-276, 0x43665da9754a5d75L, 0x263a51c4a7f0ad3bL); // 5^-65
        p(-274, 0x543ff513d29cf4d2L, 0x4fc8e635d1ecd88aL); // 5^-64
        p(-272, 0x694ff258c7443207L, 0x23bb1fc346680eacL); // 5^-63
        p(-269, 0x41d1f7777c8a9f44L, 0x4654f3da0c01092cL); // 5^-62
        p(-267, 0x524675555bad4715L, 0x57ea30d08f014b76L); // 5^-61
        p(-265, 0x66d812aab29898dbL, 0x0de4bd04b2c19e54L); // 5^-60
        p(-262, 0x40470baaaf9f5f88L, 0x78aef622efb902f5L); // 5^-59
        p(-260, 0x5058ce955b87376bL, 0x16dab3ababa743b2L); // 5^-58
        p(-258, 0x646f023ab2690545L, 0x7c9160969691149eL); // 5^-57
        p(-256, 0x7d8ac2c95f034697L, 0x3bb5b8bc3c3559c5L); // 5^-56
        p(-253, 0x4e76b9bddb620c1eL, 0x55519375a5a1581bL); // 5^-55
        p(-251, 0x6214682d523a8f26L, 0x2aa5f8530f09ae22L); // 5^-54
        p(-249, 0x7a998238a6c932efL, 0x754f7667d2cc19abL); // 5^-53
        p(-246, 0x4c9ff163683dbfd5L, 0x7951aa00e3bf900bL); // 5^-52
        p(-244, 0x5fc7edbc424d2fcbL, 0x37a614811caf740dL); // 5^-51
        p(-242, 0x77b9e92b52e07bbeL, 0x258f99a163db5111L); // 5^-50
        p(-239, 0x4ad431bb13cc4d56L, 0x7779c004de6912abL); // 5^-49
        p(-237, 0x5d893e29d8bf60acL, 0x5558300616035755L); // 5^-48
        p(-235, 0x74eb8db44eef38d7L, 0x6aae3c079b842d2aL); // 5^-47
        p(-232, 0x49133890b1558386L, 0x72ace584c1329c3bL); // 5^-46
        p(-230, 0x5b5806b4ddaae468L, 0x4f581ee5f17f4349L); // 5^-45
        p(-228, 0x722e086215159d82L, 0x632e269f6ddf141bL); // 5^-44
        p(-225, 0x475cc53d4d2d8271L, 0x5dfcd823a4ab6c91L); // 5^-43
        p(-223, 0x5933f68ca078e30eL, 0x157c0e2c8dd647b5L); // 5^-42
        p(-221, 0x6f80f42fc8971bd1L, 0x5adb11b7b14bd9a3L); // 5^-41
        p(-218, 0x45b0989ddd5e7163L, 0x08c8eb12cecf6806L); // 5^-40
        p(-216, 0x571cbec554b60dbbL, 0x6afb25d782834207L); // 5^-39
        p(-214, 0x6ce3ee76a9e3912aL, 0x65b9ef4d63241289L); // 5^-38
        p(-211, 0x440e750a2a2e3abaL, 0x5f9435905df68b96L); // 5^-37
        p(-209, 0x5512124cb4b9c969L, 0x377942f475742e7bL); // 5^-36
        p(-207, 0x6a5696dfe1e83bc3L, 0x655793b192d13a1aL); // 5^-35
        p(-204, 0x42761e4bed31255aL, 0x2f56bc4efbc2c450L); // 5^-34
        p(-202, 0x5313a5dee87d6eb0L, 0x7b2c6b62bab37564L); // 5^-33
        p(-200, 0x67d88f56a29cca5dL, 0x19f7863b696052bdL); // 5^-32
        p(-197, 0x40e7599625a1fe7aL, 0x203ab3e521dc33b6L); // 5^-31
        p(-195, 0x51212ffbaf0a7e18L, 0x684960de6a5340a4L); // 5^-30
        p(-193, 0x65697bfa9acd1d9fL, 0x025bb91604e810cdL); // 5^-29
        p(-191, 0x7ec3daf941806506L, 0x62f2a75b86221500L); // 5^-28
        p(-188, 0x4f3a68dbc8f03f24L, 0x1dd7a89933d54d20L); // 5^-27
        p(-186, 0x63090312bb2c4eedL, 0x254d92bf80caa068L); // 5^-26
        p(-184, 0x7bcb43d769f762a8L, 0x4ea0f76f60fd4882L); // 5^-25
        p(-181, 0x4d5f0a66a23a9da9L, 0x31249aa59c9e4d51L); // 5^-24
        p(-179, 0x60b6cd004ac94513L, 0x5d6dc14f03c5e0a5L); // 5^-23
        p(-177, 0x78e480405d7b9658L, 0x54c931a2c4b758cfL); // 5^-22
        p(-174, 0x4b8ed0283a6d3df7L, 0x34fdbf05baf29781L); // 5^-21
        p(-172, 0x5e72843249088d75L, 0x223d2ec729af3d62L); // 5^-20
        p(-170, 0x760f253edb4ab0d2L, 0x4acc7a78f41b0cbaL); // 5^-19
        p(-167, 0x49c97747490eae83L, 0x4ebfcc8b9890e7f4L); // 5^-18
        p(-165, 0x5c3bd5191b525a24L, 0x426fbfae7eb521f1L); // 5^-17
        p(-163, 0x734aca5f6226f0adL, 0x530baf9a1e626a6dL); // 5^-16
        p(-160, 0x480ebe7b9d58566cL, 0x43e74dc052fd8285L); // 5^-15
        p(-158, 0x5a126e1a84ae6c07L, 0x54e1213067bce326L); // 5^-14
        p(-156, 0x709709a125da0709L, 0x4a19697c81ac1befL); // 5^-13
        p(-153, 0x465e6604b7a84465L, 0x7e4fe1edd10b9175L); // 5^-12
        p(-151, 0x57f5ff85e592557fL, 0x3de3da69454e75d3L); // 5^-11
        p(-149, 0x6df37f675ef6eadfL, 0x2d5cd10396a21347L); // 5^-10
        p(-146, 0x44b82fa09b5a52cbL, 0x4c5a02a23e254c0dL); // 5^-9
        p(-144, 0x55e63b88c230e77eL, 0x3f70834acdae9f10L); // 5^-8
        p(-142, 0x6b5fca6af2bd215eL, 0x0f4ca41d811a46d4L); // 5^-7
        p(-139, 0x431bde82d7b634daL, 0x698fe69270b06c44L); // 5^-6
        p(-137, 0x53e2d6238da3c211L, 0x43f3e0370cdc8755L); // 5^-5
        p(-135, 0x68db8bac710cb295L, 0x74f0d844d013a92bL); // 5^-4
        p(-132, 0x4189374bc6a7ef9dL, 0x5916872b020c49bbL); // 5^-3
        p(-130, 0x51eb851eb851eb85L, 0x0f5c28f5c28f5c29L); // 5^-2
        p(-128, 0x6666666666666666L, 0x3333333333333334L); // 5^-1
        p(-125, 0x4000000000000000L, 0x0000000000000000L); // 5^0
        p(-123, 0x5000000000000000L, 0x0000000000000001L); // 5^1
        p(-121, 0x6400000000000000L, 0x0000000000000001L); // 5^2
        p(-119, 0x7d00000000000000L, 0x0000000000000001L); // 5^3
        p(-116, 0x4e20000000000000L, 0x0000000000000001L); // 5^4
        p(-114, 0x61a8000000000000L, 0x0000000000000001L); // 5^5
        p(-112, 0x7a12000000000000L, 0x0000000000000001L); // 5^6
        p(-109, 0x4c4b400000000000L, 0x0000000000000001L); // 5^7
        p(-107, 0x5f5e100000000000L, 0x0000000000000001L); // 5^8
        p(-105, 0x7735940000000000L, 0x0000000000000001L); // 5^9
        p(-102, 0x4a817c8000000000L, 0x0000000000000001L); // 5^10
        p(-100, 0x5d21dba000000000L, 0x0000000000000001L); // 5^11
        p(-98, 0x746a528800000000L, 0x0000000000000001L); // 5^12
        p(-95, 0x48c2739500000000L, 0x0000000000000001L); // 5^13
        p(-93, 0x5af3107a40000000L, 0x0000000000000001L); // 5^14
        p(-91, 0x71afd498d0000000L, 0x0000000000000001L); // 5^15
        p(-88, 0x470de4df82000000L, 0x0000000000000001L); // 5^16
        p(-86, 0x58d15e1762800000L, 0x0000000000000001L); // 5^17
        p(-84, 0x6f05b59d3b200000L, 0x0000000000000001L); // 5^18
        p(-81, 0x4563918244f40000L, 0x0000000000000001L); // 5^19
        p(-79, 0x56bc75e2d6310000L, 0x0000000000000001L); // 5^20
        p(-77, 0x6c6b935b8bbd4000L, 0x0000000000000001L); // 5^21
        p(-74, 0x43c33c1937564800L, 0x0000000000000001L); // 5^22
        p(-72, 0x54b40b1f852bda00L, 0x0000000000000001L); // 5^23
        p(-70, 0x69e10de76676d080L, 0x0000000000000001L); // 5^24
        p(-67, 0x422ca8b0a00a4250L, 0x0000000000000001L); // 5^25
        p(-65, 0x52b7d2dcc80cd2e4L, 0x0000000000000001L); // 5^26
        p(-63, 0x6765c793fa10079dL, 0x0000000000000001L); // 5^27
        p(-60, 0x409f9cbc7c4a04c2L, 0x1000000000000001L); // 5^28
        p(-58, 0x50c783eb9b5c85f2L, 0x5400000000000001L); // 5^29
        p(-56, 0x64f964e68233a76fL, 0x2900000000000001L); // 5^30
        p(-54, 0x7e37be2022c0914bL, 0x1340000000000001L); // 5^31
        p(-51, 0x4ee2d6d415b85aceL, 0x7c08000000000001L); // 5^32
        p(-49, 0x629b8c891b267182L, 0x5b0a000000000001L); // 5^33
        p(-47, 0x7b426fab61f00de3L, 0x31cc800000000001L); // 5^34
        p(-44, 0x4d0985cb1d3608aeL, 0x0f1fd00000000001L); // 5^35
        p(-42, 0x604be73de4838ad9L, 0x52e7c40000000001L); // 5^36
        p(-40, 0x785ee10d5da46d90L, 0x07a1b50000000001L); // 5^37
        p(-37, 0x4b3b4ca85a86c47aL, 0x04c5112000000001L); // 5^38
        p(-35, 0x5e0a1fd271287598L, 0x45f6556800000001L); // 5^39
        p(-33, 0x758ca7c70d7292feL, 0x5773eac200000001L); // 5^40
        p(-30, 0x4977e8dc68679bdfL, 0x16a872b940000001L); // 5^41
        p(-28, 0x5bd5e313828182d6L, 0x7c528f6790000001L); // 5^42
        p(-26, 0x72cb5bd86321e38cL, 0x5b67334174000001L); // 5^43
        p(-23, 0x47bf19673df52e37L, 0x79208008e8800001L); // 5^44
        p(-21, 0x59aedfc10d7279c5L, 0x7768a00b22a00001L); // 5^45
        p(-19, 0x701a97b150cf1837L, 0x3542c80deb480001L); // 5^46
        p(-16, 0x46109eced2816f22L, 0x5149bd08b30d0001L); // 5^47
        p(-14, 0x5794c6828721caebL, 0x259c2c4adfd04001L); // 5^48
        p(-12, 0x6d79f82328ea3da6L, 0x0f03375d97c45001L); // 5^49
        p(-9, 0x446c3b15f9926687L, 0x6962029a7edab201L); // 5^50
        p(-7, 0x558749db77f70029L, 0x63ba83411e915e81L); // 5^51
        p(-5, 0x6ae91c5255f4c034L, 0x1ca924116635b621L); // 5^52
        p(-2, 0x42d1b1b375b8f820L, 0x51e9b68adfe191d5L); // 5^53
        p(0, 0x53861e2053273628L, 0x6664242d97d9f64aL); // 5^54
        p(2, 0x6867a5a867f103b2L, 0x7ffd2d38fdd073dcL); // 5^55
        p(5, 0x4140c78940f6a24fL, 0x6ffe3c439ea2486aL); // 5^56
        p(7, 0x5190f96b91344ae3L, 0x6bfdcb54864ada84L); // 5^57
        p(9, 0x65f537c675815d9cL, 0x66fd3e29a7dd9125L); // 5^58
        p(11, 0x7f7285b812e1b504L, 0x00bc8db411d4f56eL); // 5^59
        p(14, 0x4fa793930bcd1122L, 0x4075d8908b251965L); // 5^60
        p(16, 0x63917877cec0556bL, 0x10934eb4adee5fbeL); // 5^61
        p(18, 0x7c75d695c2706ac5L, 0x74b82261d969f7adL); // 5^62
        p(21, 0x4dc9a61d998642bbL, 0x58f3157d27e23accL); // 5^63
        p(23, 0x613c0fa4ffe7d36aL, 0x4f2fdadc71dac97fL); // 5^64
        p(25, 0x798b138e3fe1c845L, 0x22fbd1938e517bdfL); // 5^65
        p(28, 0x4bf6ec38e7ed1d2bL, 0x25dd62fc38f2ed6cL); // 5^66
        p(30, 0x5ef4a74721e86476L, 0x0f54bbbb472fa8c6L); // 5^67
        p(32, 0x76b1d118ea627d93L, 0x5329eaaa18fb92f8L); // 5^68
        p(35, 0x4a2f22af927d8e7cL, 0x23fa32aa4f9d3bdbL); // 5^69
        p(37, 0x5cbaeb5b771cf21bL, 0x2cf8bf54e3848ad2L); // 5^70
        p(39, 0x73e9a63254e42ea2L, 0x1836ef2a1c65ad86L); // 5^71
        p(42, 0x487207df750e9d25L, 0x2f22557a51bf8c74L); // 5^72
        p(44, 0x5a8e89d75252446eL, 0x5aeaead8e62f6f91L); // 5^73
        p(46, 0x71322c4d26e6d58aL, 0x31a5a58f1fbb4b75L); // 5^74
        p(49, 0x46bf5bb038504576L, 0x3f07877973d50f29L); // 5^75
        p(51, 0x586f329c466456d4L, 0x0ec96957d0ca52f3L); // 5^76
        p(53, 0x6e8aff4357fd6c89L, 0x127bc3adc4fce7b0L); // 5^77
        p(56, 0x4516df8a16fe63d5L, 0x5b8d5a4c9b1e10ceL); // 5^78
        p(58, 0x565c976c9cbdfccbL, 0x1270b0dfc1e59502L); // 5^79
        p(60, 0x6bf3bd47c3ed7bfdL, 0x770cdd17b25efa42L); // 5^80
        p(63, 0x4378564cda746d7eL, 0x5a680a2ecf7b5c69L); // 5^81
        p(65, 0x54566be0111188deL, 0x31020cba835a3384L); // 5^82
        p(67, 0x696c06d81555eb15L, 0x7d428fe92430c065L); // 5^83
        p(70, 0x41e384470d55b2edL, 0x5e4999f1b69e783fL); // 5^84
        p(72, 0x525c6558d0ab1fa9L, 0x15dc006e2446164fL); // 5^85
        p(74, 0x66f37eaf04d5e793L, 0x3b530089ad579be2L); // 5^86
        p(77, 0x40582f2d6305b0bcL, 0x1513e0560c56c16eL); // 5^87
        p(79, 0x506e3af8bbc71cebL, 0x1a58d86b8f6c71c9L); // 5^88
        p(81, 0x6489c9b6eab8e426L, 0x00ef0e8673478e3bL); // 5^89
        p(83, 0x7dac3c24a5671d2fL, 0x412ad228101971c9L); // 5^90
        p(86, 0x4e8ba596e760723dL, 0x58bac3590a0fe71eL); // 5^91
        p(88, 0x622e8efca1388ecdL, 0x0ee9742f4c93e0e6L); // 5^92
        p(90, 0x7aba32bbc986b280L, 0x32a3d13b1fb8d91fL); // 5^93
        p(93, 0x4cb45fb55df42f90L, 0x1fa662c4f3d387b3L); // 5^94
        p(95, 0x5fe177a2b5713b74L, 0x278ffb7630c869a0L); // 5^95
        p(97, 0x77d9d58b62cd8a51L, 0x3173fa53bcfa8408L); // 5^96
        p(100, 0x4ae825771dc07672L, 0x6ee87c74561c9285L); // 5^97
        p(102, 0x5da22ed4e530940fL, 0x4aa29b916ba3b726L); // 5^98
        p(104, 0x750aba8a1e7cb913L, 0x3d4b4275c68ca4f0L); // 5^99
        p(107, 0x4926b496530df3acL, 0x164f09899c17e716L); // 5^100
        p(109, 0x5b7061bbe7d17097L, 0x1be2cbec031de0dcL); // 5^101
        p(111, 0x724c7a2ae1c5ccbdL, 0x02db7ee703e55912L); // 5^102
        p(114, 0x476fcc5acd1b9ff6L, 0x11c92f50626f57acL); // 5^103
        p(116, 0x594bbf71806287f3L, 0x563b7b247b0b2d96L); // 5^104
        p(118, 0x6f9eaf4de07b29f0L, 0x4bca59ed99cdf8fcL); // 5^105
        p(121, 0x45c32d90ac4cfa36L, 0x2f5e78348020bb9eL); // 5^106
        p(123, 0x5733f8f4d76038c3L, 0x7b361641a028ea85L); // 5^107
        p(125, 0x6d00f7320d3846f4L, 0x7a039bd208332526L); // 5^108
        p(128, 0x44209a7f48432c59L, 0x0c424163451ff738L); // 5^109
        p(130, 0x5528c11f1a53f76fL, 0x2f52d1bc1667f506L); // 5^110
        p(132, 0x6a72f166e0e8f54bL, 0x1b27862b1c01f247L); // 5^111
        p(135, 0x4287d6e04c91994fL, 0x00f8b3daf181376dL); // 5^112
        p(137, 0x5329cc985fb5ffa2L, 0x6136e0d1ade18548L); // 5^113
        p(139, 0x67f43fbe77a37f8bL, 0x398499061959e699L); // 5^114
        p(142, 0x40f8a7d70ac62fb7L, 0x13f2dfa3cfd83020L); // 5^115
        p(144, 0x5136d1cccd77bba4L, 0x78ef978cc3ce3c28L); // 5^116
        p(146, 0x6584864000d5aa8eL, 0x172b7d6ff4c1cb32L); // 5^117
        p(148, 0x7ee5a7d0010b1531L, 0x5cf65ccbf1f23dfeL); // 5^118
        p(151, 0x4f4f88e200a6ed3fL, 0x0a19f9ff773766bfL); // 5^119
        p(153, 0x63236b1a80d0a88eL, 0x6ca0787f5505406fL); // 5^120
        p(155, 0x7bec45e12104d2b2L, 0x47c8969f2a46908aL); // 5^121
        p(158, 0x4d73abacb4a303afL, 0x4cdd5e237a6c1a57L); // 5^122
        p(160, 0x60d09697e1cbc49bL, 0x4014b5ac590720ecL); // 5^123
        p(162, 0x7904bc3dda3eb5c2L, 0x3019e3176f48e927L); // 5^124
        p(165, 0x4ba2f5a6a8673199L, 0x3e102deea58d91b9L); // 5^125
        p(167, 0x5e8bb3105280fdffL, 0x6d94396a4ef0f627L); // 5^126
        p(169, 0x762e9fd467213d7fL, 0x68f947c4e2ad33b0L); // 5^127
        p(172, 0x49dd23e4c074c66fL, 0x719bccdb0dac404eL); // 5^128
        p(174, 0x5c546cddf091f80bL, 0x6e02c011d1175062L); // 5^129
        p(176, 0x736988156cb6760eL, 0x69837016455d247aL); // 5^130
        p(179, 0x4821f50d63f209c9L, 0x21f2260deb5a36ccL); // 5^131
        p(181, 0x5a2a7250bcee8c3bL, 0x4a6eaf916630c47fL); // 5^132
        p(183, 0x70b50ee4ec2a2f4aL, 0x3d0a5b75bfbcf59fL); // 5^133
        p(186, 0x4671294f139a5d8eL, 0x4626792997d61984L); // 5^134
        p(188, 0x580d73a2d880f4f2L, 0x17b01773fdcb9fe4L); // 5^135
        p(190, 0x6e10d08b8ea1322eL, 0x5d9c1d50fd3e87ddL); // 5^136
        p(193, 0x44ca82573924bf5dL, 0x1a8192529e4714ebL); // 5^137
        p(195, 0x55fd22ed076def34L, 0x4121f6e745d8da25L); // 5^138
        p(197, 0x6b7c6ba849496b01L, 0x516a74a1174f10aeL); // 5^139
        p(200, 0x432dc3492dcde2e1L, 0x02e288e4ae916a6dL); // 5^140
        p(202, 0x53f9341b79415b99L, 0x239b2b1dda35c508L); // 5^141
        p(204, 0x68f781225791b27fL, 0x4c81f5e550c3364aL); // 5^142
        p(207, 0x419ab0b576bb0f8fL, 0x5fd139af527a01efL); // 5^143
        p(209, 0x52015ce2d469d373L, 0x57c5881b2718826aL); // 5^144
        p(211, 0x6681b41b89844850L, 0x4db6ea21f0dea304L); // 5^145
        p(214, 0x4011109135f2ad32L, 0x30925255368b25e3L); // 5^146
        p(216, 0x501554b5836f587eL, 0x7cb6e6ea842def5cL); // 5^147
        p(218, 0x641aa9e2e44b2e9eL, 0x5be4a0a525396b32L); // 5^148
        p(220, 0x7d21545b9d5dfa46L, 0x32ddc8ce6e87c5ffL); // 5^149
        p(223, 0x4e34d4b9425abc6bL, 0x7fca9d810514dbbfL); // 5^150
        p(225, 0x61c209e792f16b86L, 0x7fbd44e1465a12afL); // 5^151
        p(227, 0x7a328c6177adc668L, 0x5fac961997f0975bL); // 5^152
        p(230, 0x4c5f97bceacc9c01L, 0x3bcbddcffef65e99L); // 5^153
        p(232, 0x5f777dac257fc301L, 0x6abed543feb3f63fL); // 5^154
        p(234, 0x77555d172edfb3c2L, 0x256e8a94fe60f3cfL); // 5^155
        p(237, 0x4a955a2e7d4bd059L, 0x3765169d1efc9861L); // 5^156
        p(239, 0x5d3ab0ba1c9ec46fL, 0x653e5c4466bbbe7aL); // 5^157
        p(241, 0x74895ce8a3c6758bL, 0x5e8df355806aae18L); // 5^158
        p(244, 0x48d5da11665c0977L, 0x2b18b8157042accfL); // 5^159
        p(246, 0x5b0b5095bff30bd5L, 0x15dee61acc535803L); // 5^160
        p(248, 0x71ce24bb2fefcecaL, 0x3b569fa17f682e03L); // 5^161
        p(251, 0x4720d6f4fdf5e13eL, 0x451623c4efa11cc2L); // 5^162
        p(253, 0x58e90cb23d73598eL, 0x165bacb62b8963f3L); // 5^163
        p(255, 0x6f234fdeccd02ff1L, 0x5bf297e3b66bbcefL); // 5^164
        p(258, 0x457611eb40021df7L, 0x09779eee52035616L); // 5^165
        p(260, 0x56d396661002a574L, 0x6bd586a9e6842b9bL); // 5^166
        p(262, 0x6c887bff94034ed2L, 0x06cae85460253682L); // 5^167
        p(265, 0x43d54d7fbc821143L, 0x243ed134bc174211L); // 5^168
        p(267, 0x54caa0dfaba29594L, 0x0d4e8581eb1d1295L); // 5^169
        p(269, 0x69fd4917968b3af9L, 0x10a226e265e4573bL); // 5^170
        p(272, 0x423e4daebe1704dbL, 0x5a65584d7faeb685L); // 5^171
        p(274, 0x52cde11a6d9cc612L, 0x50feae60df9a6426L); // 5^172
        p(276, 0x678159610903f797L, 0x253e59f91780fd2fL); // 5^173
        p(279, 0x40b0d7dca5a27abeL, 0x4746f83baeb09e3eL); // 5^174
        p(281, 0x50dd0dd3cf0b196eL, 0x1918b64a9a5cc5cdL); // 5^175
        p(283, 0x65145148c2cddfc9L, 0x5f5ee3dd40f3f740L); // 5^176
        p(285, 0x7e59659af38157bcL, 0x17369cd49130f510L); // 5^177
        p(288, 0x4ef7df80d830d6d5L, 0x4e822204dabe992aL); // 5^178
        p(290, 0x62b5d7610e3d0c8bL, 0x0222aa86116e3f75L); // 5^179
        p(292, 0x7b634d3951cc4fadL, 0x62ab552795c9cf52L); // 5^180
        p(295, 0x4d1e1043d31fb1ccL, 0x4dab1538bd9e2193L); // 5^181
        p(297, 0x60659454c7e79e3fL, 0x6115da86ed05a9f8L); // 5^182
        p(299, 0x787ef969f9e185cfL, 0x595b5128a8471476L); // 5^183
        p(302, 0x4b4f5be23c2cf3a1L, 0x67d912b9692c6ccaL); // 5^184
        p(304, 0x5e2332dacb38308aL, 0x21cf5767c37787fcL); // 5^185
        p(306, 0x75abff917e063cacL, 0x6a432d41b45569fbL); // 5^186
        p(309, 0x498b7fbaeec3e5ecL, 0x0269fc4910b5623dL); // 5^187
        p(311, 0x5bee5fa9aa74df67L, 0x03047b5b54e2baccL); // 5^188
        p(313, 0x72e9f79415121740L, 0x63c59a322a1b697fL); // 5^189
        p(316, 0x47d23abc8d2b4e88L, 0x3e5b805f5a5121f0L); // 5^190
        p(318, 0x59c6c96bb076222aL, 0x4df2607730e56a6cL); // 5^191
        p(320, 0x70387bc69c93aab5L, 0x216ef894fd1ec506L); // 5^192
        p(323, 0x46234d5c21dc4ab1L, 0x24e55b5d1e333b24L); // 5^193
        p(325, 0x57ac20b32a535d5dL, 0x4e1eb23465c009edL); // 5^194
        p(327, 0x6d9728dff4e834b5L, 0x01a65ec17f300c68L); // 5^195
        p(330, 0x447e798bf91120f1L, 0x1107fb38ef7e07c1L); // 5^196
        p(332, 0x559e17eef755692dL, 0x3549fa072b5d89b1L); // 5^197
        p(334, 0x6b059deab52ac378L, 0x629c7888f634ec1eL); // 5^198
        p(337, 0x42e382b2b13aba2bL, 0x3da1cb5599e11393L); // 5^199
        p(339, 0x539c635f5d8968b6L, 0x2d0a3e2b00595877L); // 5^200
        p(341, 0x68837c3734ebc2e3L, 0x784ccdb5c06fae95L); // 5^201
        p(344, 0x41522da2811359ceL, 0x3b3000919845cd1dL); // 5^202
        p(346, 0x51a6b90b21583042L, 0x09fc00b5fe574065L); // 5^203
        p(348, 0x6610674de9ae3c52L, 0x4c7b00e37ded107eL); // 5^204
        p(350, 0x7f9481216419cb67L, 0x1f99c11c5d68549dL); // 5^205
        p(353, 0x4fbcd0b4de901f20L, 0x43c018b1ba6134e2L); // 5^206
        p(355, 0x63ac04e2163426e8L, 0x54b01ede28f9821bL); // 5^207
        p(357, 0x7c97061a9bc130a2L, 0x69dc2695b337e2a1L); // 5^208
        p(360, 0x4dde63d0a158be65L, 0x6229981d9002eda5L); // 5^209
        p(362, 0x6155fcc4c9aeedffL, 0x1ab3fe24f403a90eL); // 5^210
        p(364, 0x79ab7bf5fc1aa97fL, 0x0160fdae31049351L); // 5^211
        p(367, 0x4c0b2d79bd90a9efL, 0x30dc9e8cdea2dc13L); // 5^212
        p(369, 0x5f0df8d82cf4d46bL, 0x1d13c630164b9318L); // 5^213
        p(371, 0x76d1770e38320986L, 0x0458b7bc1bde77ddL); // 5^214
        p(374, 0x4a42ea68e31f45f3L, 0x62b772d5916b0aebL); // 5^215
        p(376, 0x5cd3a5031be71770L, 0x5b654f8af5c5cda5L); // 5^216
        p(378, 0x74088e43e2e0dd4cL, 0x723ea36db337410eL); // 5^217
        p(381, 0x488558ea6dcc8a50L, 0x07672624900288a9L); // 5^218
        p(383, 0x5aa6af25093face4L, 0x0940efadb4032ad3L); // 5^219
        p(385, 0x71505aee4b8f981dL, 0x0b912b992103f588L); // 5^220
        p(388, 0x46d238d4ef39bf12L, 0x173abb3fb4a27975L); // 5^221
        p(390, 0x5886c70a2b082ed6L, 0x5d096a0fa1cb17d2L); // 5^222
        p(392, 0x6ea878ccb5ca3a8cL, 0x344bc4938a3dddc7L); // 5^223
        p(395, 0x45294b7ff19e6497L, 0x60af5adc3666aa9cL); // 5^224
        p(397, 0x56739e5fee05fdbdL, 0x58db319344005543L); // 5^225
        p(399, 0x6c1085f7e9877d2dL, 0x0f11fdf815006a94L); // 5^226
        p(402, 0x438a53baf1f4ae3cL, 0x196b3ebb0d20429dL); // 5^227
        p(404, 0x546ce8a9ae71d9cbL, 0x1fc60e69d0685344L); // 5^228
        p(406, 0x698822d41a0e503eL, 0x07b7920444826815L); // 5^229
        p(409, 0x41f515c49048f226L, 0x64d2bb42aad1810dL); // 5^230
        p(411, 0x52725b35b45b2eb0L, 0x3e076a135585e150L); // 5^231
        p(413, 0x670ef2032171fa5cL, 0x4d8944982ae759a4L); // 5^232
        p(416, 0x40695741f4e73c79L, 0x7075cadf1ad09807L); // 5^233
        p(418, 0x5083ad1272210b98L, 0x2c933d96e184be08L); // 5^234
        p(420, 0x64a498570ea94e7eL, 0x37b80cfc99e5ed8aL); // 5^235
        p(422, 0x7dcdbe6cd253a21eL, 0x05a6103bc05f68edL); // 5^236
        p(425, 0x4ea0970403744552L, 0x6387ca25583ba194L); // 5^237
        p(427, 0x6248bcc5045156a7L, 0x3c69bcaeae4a89f9L); // 5^238
        p(429, 0x7adaebf64565ac51L, 0x2b842bda59dd2c77L); // 5^239
        p(432, 0x4cc8d379eb5f8bb2L, 0x6b329b68782a3bcbL); // 5^240
        p(434, 0x5ffb085866376e9fL, 0x45ff42429634cabdL); // 5^241
        p(436, 0x77f9ca6e7fc54a47L, 0x377f12d33bc1fd6dL); // 5^242
        p(439, 0x4afc1e850fdb4e6cL, 0x52af6bc405593e64L); // 5^243
        p(441, 0x5dbb262653d22207L, 0x675b46b506af8dfdL); // 5^244
        p(443, 0x7529efafe8c6aa89L, 0x61321862485b717cL); // 5^245
        p(446, 0x493a35cdf17c2a96L, 0x0cbf4f3d6d3926eeL); // 5^246
        p(448, 0x5b88c3416ddb353bL, 0x4fef230cc88770a9L); // 5^247
        p(450, 0x726af411c952028aL, 0x43eaebcffaa94cd3L); // 5^248
        p(453, 0x4782d88b1dd34196L, 0x4a72d361fca9d004L); // 5^249
        p(455, 0x59638eade54811fcL, 0x1d0f883a7bd44405L); // 5^250
        p(457, 0x6fbc72595e9a167bL, 0x24536a491ac95506L); // 5^251
        p(460, 0x45d5c777db204e0dL, 0x06b4226db0bdd524L); // 5^252
        p(462, 0x574b3955d1e86190L, 0x28612b091ced4a6dL); // 5^253
        p(464, 0x6d1e07ab466279f4L, 0x327975cb64289d08L); // 5^254
        p(467, 0x4432c4cb0bfd8c38L, 0x5f8be99f1e996225L); // 5^255
        p(469, 0x553f75fdcefcef46L, 0x776ee406e63fbaaeL); // 5^256
        p(471, 0x6a8f537d42bc2b18L, 0x554a9d089fcfa95aL); // 5^257
        p(474, 0x4299942e49b59aefL, 0x354ea22563e1c9d8L); // 5^258
        p(476, 0x533ff939dc2301abL, 0x22a24aaebcda3c4eL); // 5^259
        p(478, 0x680ff788532bc216L, 0x0b4add5a6c10cb62L); // 5^260
        p(481, 0x4109fab533fb594dL, 0x670eca58838a7f1dL); // 5^261
        p(483, 0x514c796280fa2fa1L, 0x20d27ceea46d1ee4L); // 5^262
        p(485, 0x659f97bb2138bb89L, 0x49071c2a4d88669dL); // 5^263
        p(487, 0x7f077da9e986ea6bL, 0x7b48e334e0ea8045L); // 5^264
        p(490, 0x4f64ae8a31f45283L, 0x3d0d8e010c92902bL); // 5^265
        p(492, 0x633dda2cbe716724L, 0x2c50f1814fb73436L); // 5^266
        p(494, 0x7c0d50b7ee0dc0edL, 0x37652de1a3a50143L); // 5^267
        p(497, 0x4d885272f4c89894L, 0x329f3cad064720caL); // 5^268
        p(499, 0x60ea670fb1fabeb9L, 0x3f470bd847d8e8fdL); // 5^269
        p(501, 0x792500d39e796e67L, 0x6f18cece59cf233cL); // 5^270
        p(504, 0x4bb72084430be500L, 0x756f8140f8217605L); // 5^271
        p(506, 0x5ea4e8a553cede41L, 0x12cb61913629d387L); // 5^272
        p(508, 0x764e22cea8c295d1L, 0x377e39f583b44868L); // 5^273
        p(511, 0x49f0d5c129799da2L, 0x72aee4397250ad41L); // 5^274
        p(513, 0x5c6d0b3173d8050bL, 0x4f5a9d47cee4d891L); // 5^275
        p(515, 0x73884dfdd0ce064eL, 0x43314499c29e0eb6L); // 5^276
        p(518, 0x483530bea280c3f1L, 0x09fecae019a2c932L); // 5^277
        p(520, 0x5a427cee4b20f4edL, 0x2c7e7d98200b7b7eL); // 5^278
        p(522, 0x70d31c29dde93228L, 0x579e1cfe280e5a5dL); // 5^279
        p(525, 0x4683f19a2ab1bf59L, 0x36c2d21ed908f87bL); // 5^280
        p(527, 0x5824ee00b55e2f2fL, 0x647386a68f4b3699L); // 5^281
        p(529, 0x6e2e2980e2b5bafbL, 0x5d906850331e043fL); // 5^282
        p(532, 0x44dcd9f08db194ddL, 0x2a7a41321ff2c2a8L); // 5^283
        p(534, 0x5614106cb11dfa14L, 0x5518d17ea7ef7352L); // 5^284
        p(536, 0x6b991487dd657899L, 0x6a5f05de51eb5026L); // 5^285
        p(539, 0x433facd4ea5f6b60L, 0x127b63aaf3331218L); // 5^286
        p(541, 0x540f980a24f74638L, 0x171a3c95afffd69eL); // 5^287
        p(543, 0x69137e0cae3517c6L, 0x1ce0cbbb1bffcc45L); // 5^288
        p(546, 0x41ac2ec7ece12edbL, 0x720c7f54f17fdfabL); // 5^289
        p(548, 0x52173a79e8197a92L, 0x6e8f9f2a2ddfd796L); // 5^290
        p(550, 0x669d0918621fd937L, 0x4a3386f4b957cd7bL); // 5^291
        p(553, 0x402225af3d53e7c2L, 0x5e603458f3d6e06dL); // 5^292
        p(555, 0x502aaf1b0ca8e1b3L, 0x35f8416f30cc9888L); // 5^293
        p(557, 0x64355ae1cfd31a20L, 0x237651cafcffbeaaL); // 5^294
        p(559, 0x7d42b19a43c7e0a8L, 0x2c53e63dbc3fae55L); // 5^295
        p(562, 0x4e49af006a5cec69L, 0x1bb46fe695a7ccf5L); // 5^296
        p(564, 0x61dc1ac084f42783L, 0x42a18be03b11c033L); // 5^297
        p(566, 0x7a532170a6313164L, 0x3349eed849d6303fL); // 5^298
        p(569, 0x4c73f4e667debedeL, 0x600e35472e25de28L); // 5^299
        p(571, 0x5f90f22001d66e96L, 0x3811c298f9af55b1L); // 5^300
        p(573, 0x77752ea8024c0a3cL, 0x0616333f381b2b1eL); // 5^301
        p(576, 0x4aa93d29016f8665L, 0x43cde0078310faf3L); // 5^302
        p(578, 0x5d538c7341cb67feL, 0x74c1580963d539afL); // 5^303
        p(580, 0x74a86f90123e41feL, 0x51f1ae0bbcca881bL); // 5^304
        p(583, 0x48e945ba0b66e93fL, 0x13370cc755fe9511L); // 5^305
        p(585, 0x5b2397288e40a38eL, 0x7804cff92b7e3a55L); // 5^306
        p(587, 0x71ec7cf2b1d0cc72L, 0x560603f7765dc8eaL); // 5^307
        p(590, 0x4733ce17af227fc7L, 0x55c3c27aa9fa9d93L); // 5^308
        p(592, 0x5900c19d9aeb1fb9L, 0x4b34b319547944f7L); // 5^309
        p(594, 0x6f40f20501a5e7a7L, 0x7e01dfdfa9979635L); // 5^310
        p(597, 0x458897432107b0c8L, 0x7ec12bebc9febde1L); // 5^311
        p(599, 0x56eabd13e9499cfbL, 0x1e7176e6bc7e6d59L); // 5^312
        p(601, 0x6ca56c58e39c043aL, 0x060dd4a06b9e08b0L); // 5^313
        p(604, 0x43e763b78e4182a4L, 0x23c8a4e44342c56eL); // 5^314
        p(606, 0x54e13ca571d1e34dL, 0x2cbace1d541376c9L); // 5^315
        p(608, 0x6a198bcece465c20L, 0x57e981a4a918547bL); // 5^316
        p(611, 0x424ff76140ebf994L, 0x36f1f106e9af34cdL); // 5^317
        p(613, 0x52e3f5399126f7f9L, 0x44ae6d48a41b0201L); // 5^318
        p(615, 0x679cf287f570b5f7L, 0x75da089acd21c281L); // 5^319
        p(618, 0x40c21794f96671baL, 0x79a84560c0351991L); // 5^320
        p(620, 0x50f29d7a37c00e29L, 0x581256b8f0425ff5L); // 5^321
        p(622, 0x652f44d8c5b011b4L, 0x0e16ec672c52f7f2L); // 5^322
        p(624, 0x7e7b160ef71c1621L, 0x119ca780f767b5eeL); // 5^323
        p(627, 0x4f0cedc95a718dd4L, 0x5b01e8b09aa0d1b5L); // 5^324
    }

    static BigDecimal toBigDecimal(boolean sgn, long d, int r) {
        return new BigDecimal(BigInteger.valueOf(sgn ? -d : d), -r);
    }

    static BigDecimal toDecimal(double v) {
        assert Double.isFinite(v);
        if (v == 0.0) {
            return BigDecimal.ZERO;
        }
        long bits = Double.doubleToRawLongBits(v);
        boolean sgn = bits < 0;
        int expf = ((int) (bits >> 52) & 0x7ff);
        long manf = bits & 0xfffffffffffffL;
        int q = expf == 0 ? -1074 : expf - 1075;
        BigInteger c = BigInteger.valueOf(expf == 0
                ? manf
                : manf + 0x10000000000000L);
        boolean odd = c.testBit(0);
        int out = odd ? 1 : 0;
        int qb;
        BigInteger cb, cbl, cbr;
        if (q == -1074 || !c.equals(BigInteger.ONE.shiftLeft(52))) {
            qb = q - 1;
            cb = c.shiftLeft(1);
            cbl = cb.subtract(BigInteger.ONE);
            cbr = cb.add(BigInteger.ONE);
        } else {
            qb = q - 2;
            cb = c.shiftLeft(2);
            cbl = cb.subtract(BigInteger.ONE);
            cbr = cb.add(BigInteger.valueOf(2));
        }
        int r = ord10pow2(qb + 1) - 1;
        NumCQ p5 = Prototype.powers5.get(-r - MIN_POW_5);
        int qq = qb + p5.q - r;
        // Fixed point approximation of Vl,V,Vr with 65 fractional digits
        int sh = -qq - 65;
        BigInteger Vl = p5.c.multiply(cbl).shiftRight(sh);
        BigInteger V = p5.c.multiply(cb).shiftRight(sh);
        BigInteger Vr = p5.c.multiply(cbr).shiftRight(sh);
        long s = V.shiftRight(65).longValue();
        long t = s + 1;
        long s10 = s / 10;
        long t10 = s10 + 1;
        if (s10 >= 10) {
            boolean uin10 = (Vl.compareTo(BigInteger.valueOf(s10 * 10).shiftLeft(65)) + out) <= 0;
            boolean win10 = (BigInteger.valueOf(t10 * 10).shiftLeft(65).compareTo(Vr) + out) <= 0;
            if (uin10 || win10) {
                if (!win10) {
                    return toBigDecimal(sgn, s10, r + 1);
                }
                if (!uin10) {
                    return toBigDecimal(sgn, t10, r + 1);
                }
                assert uin10 && win10;
                // This is possible only for powers of 2 when Rv may be wider than 10^{r+1}
                assert qb == q - 2;
                if (s10 % 10 == 0) {
                    return toBigDecimal(sgn, s10, r + 1);
                }
                if (t10 % 10 == 0) {
                    return toBigDecimal(sgn, t10, r + 1);
                }
                int cmp10 = V.compareTo(BigInteger.valueOf((s10 + t10) * 10).shiftLeft(64));
                if (cmp10 < 0) {
                    return toBigDecimal(sgn, s10, r + 1);
                }
                assert cmp10 > 0; // cmp10 == 0 doesn't happen for powers of two
                return toBigDecimal(sgn, t10, r + 1);
            }
        } else if (s10 == 0) {
            // Double.MIN_VALUE or Double.MIN_VALUE*2
            return toBigDecimal(sgn, s == 4 ? 49 : 99, r - 1);
        }
        boolean uin = (Vl.compareTo(BigInteger.valueOf(s).shiftLeft(65)) + out) <= 0;
        boolean win = (BigInteger.valueOf(t).shiftLeft(65).compareTo(Vr) + out) <= 0;
        assert uin || win; // because 10^r <= 2^q
        if (!win) {
            return toBigDecimal(sgn, s, r);
        }
        if (!uin) {
            return toBigDecimal(sgn, t, r);
        }
        int cmp = V.compareTo(BigInteger.valueOf(s + t).shiftLeft(64));
        if (cmp < 0) {
            return toBigDecimal(sgn, s, r);
        }
        if (cmp > 0) {
            return toBigDecimal(sgn, t, r);
        }
        if ((s & 1) == 0) {
            return toBigDecimal(sgn, s, r);
        }
        return toBigDecimal(sgn, t, r);
    }
}
