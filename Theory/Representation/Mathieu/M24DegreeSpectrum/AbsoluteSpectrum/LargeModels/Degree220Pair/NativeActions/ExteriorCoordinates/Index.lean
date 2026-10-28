module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.Inputs

/-!
# The 462 ordered exterior coordinates

Each table entry encodes an increasing five-subset of the eleven Golay-row
coordinates, in the lexicographic order fixed by `NativeActions/source/README.md`.
Strict increase and the explicit rank calculation are checked in the kernel.
The rank is a left inverse; the binomial cardinality then proves that every
five-subset occurs. Blocks of fourteen keep kernel lookup costs small.

Source convention: James, J. Algebra 27 (1973), 57–111; the native quotient
construction and its column convention are documented in the source README.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates

/-- Increasing five-subsets in lexicographic order, encoded with one nibble per entry. -/
def subsetCodeBlocks : Array (Array ℕ) := #[
  #[274960, 340496, 406032, 471568, 537104, 602640, 668176, 344592, 410128, 475664, 541200, 606736, 672272, 414224],
  #[479760, 545296, 610832, 676368, 483856, 549392, 614928, 680464, 553488, 619024, 684560, 623120, 688656, 692752],
  #[344848, 410384, 475920, 541456, 606992, 672528, 414480, 480016, 545552, 611088, 676624, 484112, 549648, 615184],
  #[680720, 553744, 619280, 684816, 623376, 688912, 693008, 414736, 480272, 545808, 611344, 676880, 484368, 549904],
  #[615440, 680976, 554000, 619536, 685072, 623632, 689168, 693264, 484624, 550160, 615696, 681232, 554256, 619792],
  #[685328, 623888, 689424, 693520, 554512, 620048, 685584, 624144, 689680, 693776, 624400, 689936, 694032, 694288],
  #[344864, 410400, 475936, 541472, 607008, 672544, 414496, 480032, 545568, 611104, 676640, 484128, 549664, 615200],
  #[680736, 553760, 619296, 684832, 623392, 688928, 693024, 414752, 480288, 545824, 611360, 676896, 484384, 549920],
  #[615456, 680992, 554016, 619552, 685088, 623648, 689184, 693280, 484640, 550176, 615712, 681248, 554272, 619808],
  #[685344, 623904, 689440, 693536, 554528, 620064, 685600, 624160, 689696, 693792, 624416, 689952, 694048, 694304],
  #[414768, 480304, 545840, 611376, 676912, 484400, 549936, 615472, 681008, 554032, 619568, 685104, 623664, 689200],
  #[693296, 484656, 550192, 615728, 681264, 554288, 619824, 685360, 623920, 689456, 693552, 554544, 620080, 685616],
  #[624176, 689712, 693808, 624432, 689968, 694064, 694320, 484672, 550208, 615744, 681280, 554304, 619840, 685376],
  #[623936, 689472, 693568, 554560, 620096, 685632, 624192, 689728, 693824, 624448, 689984, 694080, 694336, 554576],
  #[620112, 685648, 624208, 689744, 693840, 624464, 690000, 694096, 694352, 624480, 690016, 694112, 694368, 694384],
  #[344865, 410401, 475937, 541473, 607009, 672545, 414497, 480033, 545569, 611105, 676641, 484129, 549665, 615201],
  #[680737, 553761, 619297, 684833, 623393, 688929, 693025, 414753, 480289, 545825, 611361, 676897, 484385, 549921],
  #[615457, 680993, 554017, 619553, 685089, 623649, 689185, 693281, 484641, 550177, 615713, 681249, 554273, 619809],
  #[685345, 623905, 689441, 693537, 554529, 620065, 685601, 624161, 689697, 693793, 624417, 689953, 694049, 694305],
  #[414769, 480305, 545841, 611377, 676913, 484401, 549937, 615473, 681009, 554033, 619569, 685105, 623665, 689201],
  #[693297, 484657, 550193, 615729, 681265, 554289, 619825, 685361, 623921, 689457, 693553, 554545, 620081, 685617],
  #[624177, 689713, 693809, 624433, 689969, 694065, 694321, 484673, 550209, 615745, 681281, 554305, 619841, 685377],
  #[623937, 689473, 693569, 554561, 620097, 685633, 624193, 689729, 693825, 624449, 689985, 694081, 694337, 554577],
  #[620113, 685649, 624209, 689745, 693841, 624465, 690001, 694097, 694353, 624481, 690017, 694113, 694369, 694385],
  #[414770, 480306, 545842, 611378, 676914, 484402, 549938, 615474, 681010, 554034, 619570, 685106, 623666, 689202],
  #[693298, 484658, 550194, 615730, 681266, 554290, 619826, 685362, 623922, 689458, 693554, 554546, 620082, 685618],
  #[624178, 689714, 693810, 624434, 689970, 694066, 694322, 484674, 550210, 615746, 681282, 554306, 619842, 685378],
  #[623938, 689474, 693570, 554562, 620098, 685634, 624194, 689730, 693826, 624450, 689986, 694082, 694338, 554578],
  #[620114, 685650, 624210, 689746, 693842, 624466, 690002, 694098, 694354, 624482, 690018, 694114, 694370, 694386],
  #[484675, 550211, 615747, 681283, 554307, 619843, 685379, 623939, 689475, 693571, 554563, 620099, 685635, 624195],
  #[689731, 693827, 624451, 689987, 694083, 694339, 554579, 620115, 685651, 624211, 689747, 693843, 624467, 690003],
  #[694099, 694355, 624483, 690019, 694115, 694371, 694387, 554580, 620116, 685652, 624212, 689748, 693844, 624468],
  #[690004, 694100, 694356, 624484, 690020, 694116, 694372, 694388, 624485, 690021, 694117, 694373, 694389, 694390]]

/-- The `k`th member of the `i`th increasing five-subset. -/
def fiveTuple (i : Fin 462) (k : Fin 5) : Fin 11 :=
  Fin.ofNat 11 (((subsetCodeBlocks[i.val / 14]!)[i.val % 14]! >>> (4 * k.val)) % 16)

lemma fiveTuple_strictMono (i : Fin 462) : StrictMono (fiveTuple i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have h : ∀ (i : Fin 462) (k : Fin 4),
      fiveTuple i k.castSucc < fiveTuple i k.succ := by decide +kernel
  exact h i

def fiveEmbedding (i : Fin 462) : Fin 5 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono (fiveTuple i) (fiveTuple_strictMono i)

/-- The zero-based lexicographic rank of an increasing five-tuple. -/
def fiveRank (v : Fin 5 → Fin 11) : ℕ :=
  461 - (Nat.choose (10 - (v 0).val) 5 + Nat.choose (10 - (v 1).val) 4 +
    Nat.choose (10 - (v 2).val) 3 + Nat.choose (10 - (v 3).val) 2 +
    Nat.choose (10 - (v 4).val) 1)

lemma fiveRank_fiveTuple : ∀ i : Fin 462, fiveRank (fiveTuple i) = i.val := by
  decide +kernel

lemma fiveEmbedding_injective : Function.Injective fiveEmbedding := by
  intro i j hij
  apply Fin.ext
  rw [← fiveRank_fiveTuple i, ← fiveRank_fiveTuple j]
  have h : fiveTuple i = fiveTuple j := congrArg DFunLike.coe hij
  rw [h]

noncomputable def fiveSubsetEquiv : Fin 462 ≃ Set.powersetCard (Fin 11) 5 :=
  Equiv.ofBijective (fun i => Set.powersetCard.ofFinEmbEquiv (fiveEmbedding i)) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨Set.powersetCard.ofFinEmbEquiv.injective.comp fiveEmbedding_injective, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Set.powersetCard.card]
    simp only [Nat.card_fin]
    decide)

lemma fiveSubsetEquiv_embedding (i : Fin 462) :
    Set.powersetCard.ofFinEmbEquiv.symm (fiveSubsetEquiv i) = fiveEmbedding i :=
  Set.powersetCard.ofFinEmbEquiv.symm_apply_apply _

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
