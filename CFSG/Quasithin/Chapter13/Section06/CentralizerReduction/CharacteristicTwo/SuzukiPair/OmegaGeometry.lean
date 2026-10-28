module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Setup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Alignment
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.AlignFactors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Covered
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.KernelAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.ThompsonComparison
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Reduction

/-!
# Covered omega geometry for the paired Suzuki branch

The supporting modules construct the Sylow equalities, retain both actual
component embeddings under alignment, and prove that Ω₁(T₀) is elementary
abelian from the genuine earlier multiplier and involution-lifting inputs.

Square-one factor stabilizers act through square-one elements of T₀,
so they centralize its elementary omega. The maximal-order comparison
then rules out factor interchange by a largest elementary subgroup,
proving that J(Tᵥ) centralizes Ω₁(T₀).

For the normalizer step, decompose C_{Tᵥ}(Ω₁(T₀)) into its
intersection with K₀ and the kernel C_{Tᵥ}(K₀). The Borel preserves the
first subgroup and centralizes the kernel, hence normalizes their product.
B.2.3(5) then gives the required Baumann normalizer and the existing
13.6.4–5 argument places the Borel in C_{M_V}(v).

The assembled results discharge both the action-kernel decomposition and
the Thompson centralization. The original conditional interfaces are retained.
The actual component pair, elementary-center multiplier input and single-factor
involution lifting remain inputs owned by the source assembly. In particular,
the nontrivial Sz(8) covers are retained. Only normalization is asserted:
the printed normal-in-B clause would additionally require Baum(Tᵥ) ≤ B.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 / PDF p.944;
I.2.2(4), pp.409–411; B.2.3(5), p.75.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory Stellmacher CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] {T K : Subgroup G} {v : G}

/-- The actual Tᵥ action preserves Ω₁(Tᵥ ∩ K₀). -/
theorem tv_normalizes_omega : Tv T v ≤ normalizer (omega T K v : Set G) := by
  let := omega₁_characteristic (intersection T K v) (p := 2)
  have hi : Tv T v ≤ normalizer (intersection T K v : Set G) :=
    (le_inf (Tv T v).le_normalizer (le_normalizer_conjugateSpanBy K (Tv T v))).trans
      inf_normalizer_le_normalizer_inf
  exact hi.trans (normalizer_le_normalizer_characteristic_image _ (omega₁ _ (p := 2)))

variable [Finite G]

/-- Preserve the centralizing kernel when passing from T₀ to the full Tᵥ. -/
theorem Marking.borel_normalizes_centralizer_of_kernel_decomposition (d : Marking T K v)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hZ : IsPGroup 2 (center (orbit T K v)))
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter))
    (hkernel : Tv T v ⊓ centralizer (omega T K v : Set G) =
      (intersection T K v ⊓ centralizer (omega T K v : Set G)) ⊔
        (Tv T v ⊓ centralizer (orbit T K v : Set G))) :
    d.borel ≤ normalizer
      ((Tv T v ⊓ centralizer (omega T K v : Set G) : Subgroup G) : Set G) := by
  rw [hkernel]
  have hk : d.borel ≤ normalizer
      ((Tv T v ⊓ centralizer (orbit T K v : Set G) : Subgroup G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact d.borel_le_orbit.trans (le_centralizer_iff.mp inf_le_right)
  exact (le_inf (d.borel_normalizes_intersection_centralizer P hP hKG hZ ha) hk).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Apply the covered-omega calculation to the existing Baumann and local-normalizer
consumer with explicit Thompson and kernel inputs. The assembled version below
discharges both inputs from the actual paired action. -/
theorem PairFactors.borel_le_localNormalizer_of_kernel_decomposition
    {M V : Subgroup G} {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter))
    (hJ : elementaryAbelianMaxJ (Tv T v) ≤ centralizer (omega T K v : Set G))
    (hkernel : Tv T v ⊓ centralizer (omega T K v : Set G) =
      (intersection T K v ⊓ centralizer (omega T K v : Set G)) ⊔
        (Tv T v ⊓ centralizer (orbit T K v : Set G)))
    (hS : baumann T ≤ Tv T v)
    (h1325 : normalizer (baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M) :
    d.borel ≤ localNormalizer V v := by
  let := c.orbit_center_elementary hKG hK
  let := c.omega_elementary P hP hKG hK hlift ha
  have hN := d.borel_normalizes_centralizer_of_kernel_decomposition P hP hKG
    (IsElementaryAbelian.isPGroup 2 _) ha hkernel
  exact borel_le_localNormalizer d hKG hS h1325 h1226 hMV
    (normalizes_baumann_of_omega T K d.borel v hJ hN)

/-- The aligned covered pair has its elementary Thompson subgroup in the
centralizer of the actual omega. The square-one action premise of the
maximal-order comparison is discharged by the intrinsic action calculation. -/
theorem PairFactors.thompson_le_centralizer
    {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    elementaryAbelianMaxJ (Tv T v) ≤ centralizer (omega T K v : Set G) := by
  exact c.thompson_le_centralizer_of_stable_involutions P hP hKG hK hlift ha
    (c.square_one_normalizer_centralizes_omega P hP hKG hK hlift ha)

/-- The elementary omega and Thompson conclusions are intrinsic to the actual
pair. Choose compatible aligned coordinates to prove them from any marking. -/
theorem PairFactors.omega_and_thompson
    {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q) :
    IsElementaryAbelian 2 (omega T K v) ∧
      elementaryAbelianMaxJ (Tv T v) ≤ centralizer (omega T K v : Set G) := by
  obtain ⟨d', c', _, _, ha⟩ := c.exists_aligned P hP hKG
  exact ⟨c'.omega_elementary P hP hKG hK hlift ha,
    c'.thompson_le_centralizer P hP hKG hK hlift ha⟩

/-- The lifted Borel normalizes Baum(Tᵥ), using B.2.3(5) and the proved
centralizing-kernel decomposition. No containment of Baum(Tᵥ) in K₀ is used. -/
theorem PairFactors.borel_normalizes_baumann
    {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    d.borel ≤ normalizer (baumann (Tv T v) : Set G) := by
  let := c.omega_elementary P hP hKG hK hlift ha
  exact normalizes_baumann_of_omega T K d.borel v
    (c.thompson_le_centralizer P hP hKG hK hlift ha)
    (c.borel_normalizes_centralizer P hP hKG hK hlift ha)

/-- The actual paired Borel lies in C_{M_V}(v). The omega, Thompson and
normalizer geometry are proved; only the genuine earlier local inputs remain. -/
theorem PairFactors.borel_le_localNormalizer
    {M V : Subgroup G} {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter))
    (hS : baumann T ≤ Tv T v)
    (h1325 : normalizer (baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M) :
    d.borel ≤ localNormalizer V v := by
  exact SuzukiPair.borel_le_localNormalizer d hKG hS h1325 h1226 hMV
    (c.borel_normalizes_baumann P hP hKG hK hlift ha)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
