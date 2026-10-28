module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates

/-!
# Word coordinates for the characteristic Held candidates

The carrier is the existing 128-element Sylow enumeration. Multiplication follows
positive words in its seven generators, using checked right-multiplication steps.
The word and step equations identify this operation with multiplication of the
actual permutations; group laws are transported through that bijection.

These computational coordinates support the intrinsic characteristicity checks
for Huppert--Blackburn III, XII.1.18(b), printed p.314. They assert no subgroup
census or automorphism property. See `source/README.md` for data replay.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.CharacteristicCoordinates
open Subgroup

set_option maxRecDepth 100000

/-- Coordinates in the existing bijective Sylow enumeration. -/
@[expose] public def Point : Type := Fin 128
public instance : DecidableEq Point := inferInstanceAs (DecidableEq (Fin 128))
public instance : Fintype Point := inferInstanceAs (Fintype (Fin 128))
public instance : Inhabited Point := ⟨(0 : Fin 128)⟩

public instance (p : Point → Prop) [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Nat.decidableForallFin 128 p d

@[expose] public def realize (x : Point) : Model.sylowSubgroup := Model.sylowElement x

@[expose] public def inverses : Array (Fin 128) := #[0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 10, 11, 59, 58, 56, 57, 16, 17, 85, 84, 20, 21, 80, 81, 24, 70, 26, 68, 88, 78, 76, 90, 32, 33, 35, 34, 36, 37, 38, 39, 41, 40, 116, 117, 115, 114, 47, 46, 50, 100, 48, 102, 123, 109, 111, 121, 14, 15, 13, 12, 60, 61, 62, 63, 77, 91, 89, 79, 27, 69, 25, 71, 72, 94, 93, 75, 30, 64, 29, 67, 22, 23, 82, 83, 19, 18, 86, 87, 28, 66, 31, 65, 92, 74, 73, 95, 110, 120, 122, 108, 49, 103, 51, 101, 124, 106, 105, 127, 99, 53, 96, 54, 113, 112, 45, 44, 42, 43, 119, 118, 97, 55, 98, 52, 104, 126, 125, 107]

public instance : One Point := ⟨(0 : Fin 128)⟩
public instance : Inv Point := ⟨fun x => inverses[(x : Fin 128).val]!⟩

private theorem realize_one : realize 1 = 1 := by decide +kernel
@[expose] public def rightSteps : Array ℕ := #[
  118890087514369,
  303642667073920,
  110213175672835,
  312489221800066,
  338688353747717,
  400226915681156,
  347537064280583,
  391552159646342,
  215962773685513,
  453423191901576,
  224811475895307,
  444748427543690,
  488468845283085,
  532483940648844,
  479796236731919,
  541334798665358,
  330541848922385,
  409741312215440,
  321856347146259,
  418579277006994,
  128127700028181,
  295219378228116,
  136967820626455,
  286536032258710,
  14176721898777,
  163744929369496,
  5486925155355,
  172578599193754,
  93237499776797,
  365882294243228,
  102073325407775,
  357194653306526,
  344289436422433,
  388304531788192,
  335614680387619,
  397153242321058,
  106693025469221,
  308969071596452,
  115539580195367,
  300292159754918,
  463344334345513,
  560067264206248,
  472186594104363,
  551386057397418,
  243269263284013,
  428021847005100,
  234590212281903,
  436866262570670,
  41432533506353,
  278892951722416,
  50266203330611,
  270203154978994,
  208385505483573,
  498691205471156,
  199697864546871,
  507527031102134,
  477096250498361,
  538634812431800,
  485947108514875,
  529962203880634,
  221838900731709,
  441775852380092,
  213164136373823,
  450624554589886,
  99113460359489,
  354234788258240,
  90425819422787,
  363070613889218,
  2254537761605,
  169346211800004,
  11088207585863,
  160656415056582,
  86181966456137,
  376487662282184,
  77498612163659,
  385327774557386,
  24505189394253,
  156412495505356,
  33347457476175,
  147731297019598,
  134828244396369,
  284396456028624,
  126144898426963,
  293236576626898,
  319444348447573,
  416167278308308,
  328282313239127,
  407481776532182,
  29556582837593,
  143940422381016,
  20875384351835,
  152782690462938,
  73435082010461,
  381264244404188,
  82275194285663,
  372580890111710,
  197012894052705,
  504842060607968,
  205848719683683,
  496154419671266,
  47308677198693,
  267245628847076,
  38618880455271,
  276079298671334,
  184079235888489,
  527092770371048,
  192921495647339,
  518411563562218,
  69557181216621,
  254309764937708,
  60878130214511,
  263154180503278,
  232721235638641,
  434997285927408,
  241565651204211,
  426318234925298,
  470045161700213,
  549244624993268,
  461363954891383,
  558086884752118,
  57085108092281,
  259361158381048,
  65929523657851,
  250682107378938,
  188855818010493,
  514345885925372,
  180174611201663,
  523188145684222
]

@[expose] public def step (x : Point) (k : Fin 7) : Point :=
  (⟨rightSteps[(x : Fin 128).val]! / 128 ^ k.val % 128, Nat.mod_lt _ (by decide)⟩ : Fin 128)

private theorem step_realize : ∀ (x : Point) (k : Fin 7),
    realize (step x k) = realize x * generator 44 k := by decide +kernel

@[expose] public def sylowWords : Array (List (Fin 7)) := #[
  [],
  [0],
  [1],
  [0, 1],
  [5],
  [0, 5],
  [5, 1],
  [1, 5],
  [0, 1, 3],
  [1, 3],
  [0, 3],
  [3],
  [1, 3, 5],
  [3, 5, 1],
  [0, 3, 5],
  [3, 5],
  [5, 4],
  [4, 5],
  [4, 1, 5],
  [4, 5, 1],
  [4],
  [0, 4],
  [4, 1],
  [0, 4, 1],
  [1, 6, 0],
  [1, 6],
  [6, 0],
  [6],
  [4, 6, 0],
  [4, 6],
  [6, 5],
  [4, 1, 6],
  [6, 4, 6],
  [0, 6, 4, 6],
  [0, 2, 3, 5],
  [2, 3, 5],
  [4, 1, 4],
  [1, 2, 3],
  [0, 2, 3],
  [2, 3],
  [1, 3, 5, 4],
  [1, 3, 4, 5],
  [2, 5, 4],
  [2, 4, 5],
  [1, 4, 3],
  [1, 3, 4],
  [2, 4],
  [4, 2],
  [6, 3],
  [0, 6, 2],
  [2, 6],
  [0, 3, 6],
  [4, 3, 6],
  [2, 4, 6],
  [2, 6, 5],
  [0, 3, 6, 5],
  [2, 5],
  [0, 2, 5],
  [2, 5, 1],
  [1, 2, 5],
  [2],
  [0, 2],
  [1, 2],
  [0, 1, 2],
  [0, 6, 5],
  [0, 4, 1, 6],
  [0, 4, 6, 0],
  [0, 4, 6],
  [0, 6, 0],
  [0, 6],
  [2, 6, 2],
  [0, 1, 6],
  [5, 6, 5],
  [4, 6, 4],
  [0, 6, 5, 4],
  [5, 4, 6],
  [5, 6, 0],
  [5, 6],
  [0, 6, 0, 4],
  [0, 6, 4],
  [1, 4],
  [0, 1, 4],
  [1, 4, 1],
  [2, 3, 4],
  [1, 4, 5],
  [1, 5, 4],
  [1, 4, 5, 1],
  [1, 4, 1, 5],
  [6, 0, 4],
  [6, 4],
  [0, 5, 6, 0],
  [0, 5, 6],
  [6, 5, 4],
  [4, 5, 6],
  [0, 5, 6, 5],
  [0, 4, 6, 4],
  [0, 2, 6, 5],
  [3, 6, 5],
  [3, 4, 6],
  [4, 2, 6],
  [0, 2, 6],
  [3, 6],
  [0, 6, 3],
  [6, 2],
  [2, 5, 6, 5],
  [2, 4, 6, 4],
  [3, 4, 5, 6],
  [2, 5, 4, 6],
  [2, 5, 6],
  [6, 4, 3],
  [5, 6, 2],
  [3, 6, 4],
  [4, 3],
  [3, 4],
  [1, 2, 4],
  [1, 4, 2],
  [3, 4, 5],
  [3, 5, 4],
  [1, 2, 4, 5],
  [1, 2, 5, 4],
  [2, 6, 4],
  [5, 6, 3],
  [6, 4, 2],
  [3, 5, 6],
  [2, 6, 5, 4],
  [2, 4, 5, 6],
  [3, 4, 6, 4],
  [3, 5, 6, 5]
]

private theorem word_realize : ∀ x : Point,
    realize x = evalWord (generator 44) sylowWords[(x : Fin 128).val]! := by decide +kernel

private theorem fold_realize (w : List (Fin 7)) (x : Point) :
    realize (w.foldl step x) = realize x * evalWord (generator 44) w := by
  induction w generalizing x with
  | nil => exact (mul_one _).symm
  | cons k w ih =>
    rw [List.foldl_cons, ih, step_realize x k]
    exact mul_assoc _ _ _

public instance : Mul Point :=
  ⟨fun x y => (sylowWords[(y : Fin 128).val]!).foldl step x⟩

private theorem realize_mul (x y : Point) : realize (x * y) = realize x * realize y := by
  change realize ((sylowWords[(y : Fin 128).val]!).foldl step x) = _
  rw [fold_realize, ← word_realize]

private theorem inverse_product : ∀ x : Point, x⁻¹ * x = 1 := by decide +kernel

private theorem realize_inv (x : Point) : realize x⁻¹ = (realize x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← realize_mul, inverse_product, realize_one]

private theorem realize_bijective : Function.Bijective realize := Model.sylowElement_bijective

/-- The group laws are transported from the actual permutation group. -/
public instance : Group Point where
  mul_assoc x y z := by exact realize_bijective.1 (by simp only [realize_mul, mul_assoc])
  one_mul x := by exact realize_bijective.1 (by simp only [realize_mul, realize_one, one_mul])
  mul_one x := by exact realize_bijective.1 (by simp only [realize_mul, realize_one, mul_one])
  inv_mul_cancel x := by exact realize_bijective.1 (by
    simp only [realize_mul, realize_inv, realize_one, inv_mul_cancel])

/-- An actual group isomorphism, with the published enumeration as its map. -/
@[expose] public noncomputable def equiv : Point ≃* Model.sylowSubgroup :=
  { Equiv.ofBijective realize (by exact realize_bijective) with map_mul' := by exact realize_mul }


end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.CharacteristicCoordinates
