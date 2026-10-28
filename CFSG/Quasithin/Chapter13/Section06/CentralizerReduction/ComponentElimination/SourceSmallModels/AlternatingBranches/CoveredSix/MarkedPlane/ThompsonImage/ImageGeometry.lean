module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.SourceAction.Construction.Offenders
public import Theory.Representation.HexacodeAction.ThompsonOffenders
public import Theory.Representation.BinaryOffender.FixedCodimTransport

/-!
# Identifying the literal covered-six Thompson image

A moving maximum elementary subgroup exists by the commutator-generation
condition in Y_z. In the full plus action, all such nontrivial images are
best offenders in a common two-group. The concrete hexacode uniqueness
calculation identifies them, hence identifies the subgroup they generate
with J(Tᵥ)⁺. It lies in the prescribed even component and pulls back along
the actual core comparison to a four-group of K/O₂(K).

The same coordinates transport the binary fixed dimension and the full
pointwise-kernel identity. Baumann fixes these vectors, so its literal
plus image also equals this four-group. The kernel identity implies that
the full binary stabilizer normalizes the original four-group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2(8)
(printed p.86), K.1.3 (p.453), and the covered-A₆ paragraph of 13.6.22
(p.932). The source action construction and concrete finite calculations
are imported separately; the source application is in `Marking`.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection
variable {G : Type*} [Group G] [Finite G] {K L T : Subgroup G} {z v : G}
variable {h : IsExceptionalAhat6Block K} [IsElementaryAbelian 2 (blockU K)]
    {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}
    {m : HexacodeModel h} {f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz}
    (d : PlusBlockModel K L T z v h hL hz m f)

private theorem model_best {B : Subgroup (Gplus K L T z v hL hz)}
    (hB : IsBestOffender d.action B) :
    IsBestOffender Hexacode.action (B.map d.embedding) :=
  hB.map_of_fixedCodim d.action Hexacode.action d.embedding d.injective
    (fixedCodim_map_equivariant d.action Hexacode.action d.embedding
      m.coordinates d.intertwining)

/-- Every nontrivial maximum-elementary image is the same offender in the actual Tᵥ-image;
the subgroup they generate is therefore itself a best offender. -/
theorem PlusBlockModel.thompson_isBestOffender (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) :
    IsBestOffender d.action (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))) := by
  obtain ⟨E, hE, hEn⟩ := exists_maximum_moving K L T z v hK hn hL hz
  let B := plusImage K L T z v hL hz E
  have hB : IsBestOffender d.action B :=
    Construction.plusBlockModel_maxElementary_isBestOffender d hK hn hLK E hE hEn
  have hT : IsPGroup 2 (Tv T v) := by
    obtain ⟨P, hP⟩ := hK.1.2.2.1
    rw [← hP]
    exact P.isPGroup'.map (K ⊔ Tv T v).subtype
  let P := (plusImage K L T z v hL hz (Tv T v)).map d.embedding
  have hP : IsPGroup 2 P :=
    (hT.comap_subtype.map (plusMk K L T z v hL hz)).map d.embedding
  have hBP : B.map d.embedding ≤ P := map_mono (map_mono (comap_mono hE.1))
  have hEP (D : Subgroup G) (hD : D ∈ elementaryAbelianMaxSubgroups (Tv T v)) :
      plusImage K L T z v hL hz D ≤ B := by
    by_cases hDn : plusImage K L T z v hL hz D = ⊥
    · rw [hDn]; exact bot_le
    have hD' := Construction.plusBlockModel_maxElementary_isBestOffender d hK hn hLK D hD hDn
    have he := Hexacode.bestOffender_unique_in_pgroup P hP
      (map_mono (map_mono (comap_mono hD.1))) hBP (model_best d hD') (model_best d hB)
    exact (map_injective d.injective he).le
  have hJB : elementaryAbelianMaxJ (Tv T v) ≤
      (B.comap (plusMk K L T z v hL hz)).map (plusActor K L T v).subtype := by
    apply sSup_le
    intro D hD g hg
    refine ⟨⟨g, (hD.1.trans (show Tv T v ≤ plusActor K L T v from le_sup_right)) hg⟩, ?_, rfl⟩
    exact hEP D hD (mem_map_of_mem _ hg)
  have hJ : plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) = B := by
    apply le_antisymm
    · rintro a ⟨g, hg, rfl⟩
      obtain ⟨b, hb, he⟩ := hJB hg
      have hbg : b = g := Subtype.ext he
      exact hbg ▸ hb
    · exact map_mono (comap_mono (le_sSup hE))
  rw [hJ]
  exact hB
/-- The full best-offender kernel calculation survives the prescribed coordinates. -/
theorem PlusBlockModel.bestOffender_kernel
    {B : Subgroup (Gplus K L T z v hL hz)} (hB : IsBestOffender d.action B) :
    subspaceKernel d.action (fixedSpace d.action B) ⊤ = B := by
  have hmodel := model_best d hB
  have hfixed := fixedSpace_map_equivariant d.action Hexacode.action
    d.embedding m.coordinates d.intertwining B
  apply le_antisymm
  · intro g hg
    have hgm : d.embedding g ∈ B.map d.embedding := by
      rw [Hexacode.bestOffender_eq_kernel _ hmodel]
      refine ⟨mem_top _, ?_⟩
      intro w hw
      rw [← hfixed] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      exact (d.intertwining g u).symm.trans (congrArg m.coordinates (hg.2 u hu))
    obtain ⟨b, hb, he⟩ := hgm
    exact d.injective he ▸ hb
  · intro g hg
    exact ⟨mem_top _, fun u hu => hu ⟨g, hg⟩⟩

/-- Full best offenders lie in the specified component, not just an abstract even subgroup. -/
theorem PlusBlockModel.bestOffender_le_component
    {B : Subgroup (Gplus K L T z v hL hz)} (hB : IsBestOffender d.action B) :
    B ≤ f.range := by
  intro b hb
  have he := Hexacode.bestOffender_le_even _ (model_best d hB) (mem_map_of_mem _ hb)
  let e : Atlas.Codes.HexEvenAutomorphisms := ⟨d.embedding b, he⟩
  refine ⟨m.quotientIso.symm e, d.injective ?_⟩
  rw [d.component, m.quotientIso.apply_symm_apply]

/-- The two fixed-space dimensions are compared by an actual linear equivalence. -/
theorem PlusBlockModel.bestOffender_finrank
    {B : Subgroup (Gplus K L T z v hL hz)} (hB : IsBestOffender d.action B) :
    Module.finrank (ZMod 2) (fixedSpace d.action B) = 4 := by
  have he := fixedSpace_map_equivariant d.action Hexacode.action
    d.embedding m.coordinates d.intertwining B
  calc
    _ = Module.finrank (ZMod 2) ((fixedSpace d.action B).map m.coordinates.toLinearMap) :=
      (Submodule.equivMapOfInjective m.coordinates.toLinearMap m.coordinates.injective _).finrank_eq
    _ = 4 := by rw [he]; exact Hexacode.bestOffender_fixedSpace_finrank _ (model_best d hB)

/-- A constructed marking of the original Thompson and Baumann groups. -/
structure FourGroupMarking
    (K L T : Subgroup G) (z v : G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz) where
  fourGroup : Subgroup (K ⧸ pCore 2 K)
  elementary : IsElementaryAbelian 2 fourGroup
  card : Nat.card fourGroup = 4
  thompson : fourGroup.map f = plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))
  baumann : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) = fourGroup.map f
  fixed_finrank : Module.finrank (ZMod 2) (fixedSpace (binaryAction h) fourGroup) = 4
  pointwise_kernel : fourGroup = subspaceKernel (binaryAction h)
    (fixedSpace (binaryAction h) fourGroup) ⊤
  normalizes : subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) fourGroup) ≤
    normalizer (fourGroup : Set _)

include d in
/-- The actual Thompson image pulls back to the unique source four-group. -/
theorem PlusBlockModel.nonempty_fourGroupMarking
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (fi : Function.Injective f) :
    Nonempty (FourGroupMarking K L T z v h hL hz f) := by
  let B := plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))
  have hB : IsBestOffender d.action B := d.thompson_isBestOffender hK hn hLK
  let A := B.comap f
  have hA : A.map f = B := map_comap_eq_self (d.bestOffender_le_component hB)
  have hmodel := model_best d hB
  have hcard : Nat.card A = 4 := by
    calc
      _ = Nat.card (A.map f) := (card_map_of_injective fi).symm
      _ = Nat.card (B.map d.embedding) := by rw [hA, card_map_of_injective d.injective]
      _ = 4 := Hexacode.bestOffender_card _ hmodel
  let : IsElementaryAbelian 2 B := hB.1.2
  have hEA : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun a b => by
      apply Subtype.ext
      apply fi
      change f (a.val * b.val) = f (b.val * a.val)
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (mul_comm (⟨f a, a.property⟩ : B) ⟨f b, b.property⟩)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => by
      apply Subtype.ext
      apply fi
      change f (a.val ^ 2) = f 1
      simpa only [map_pow, map_one] using
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) (f a.val) a.property)) }
  have hkernel : A = subspaceKernel (binaryAction h) (fixedSpace (binaryAction h) A) ⊤ :=
    d.core_kernel_of_image fi A (by rw [hA]; exact d.bestOffender_kernel hB)
  refine ⟨⟨A, hEA, hcard, hA, ?_, ?_, hkernel,
    fixedSpace_stabilizer_le_normalizer_of_kernel K h A hkernel⟩⟩
  · rw [hA]
    exact d.baumann_eq_thompson (blockU_le_Tv K L T z v hK hn) (d.bestOffender_kernel hB)
  · rw [← d.fixedSpace_component A, hA]
    exact d.bestOffender_finrank hB
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage
