module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceAssembly
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.BeforeMoved.Supports

/-!
# Restricting an original noncyclic minimum actor to its core support

Odd splitting transports hyperplane supports and proves faithfulness on the
moved module of the literal local group PA. If restriction exhausts the
four-dimensional codimension budget, equality forces every original actor
line to have the same codimension after restriction. Original minimality
then supplies the strict inequality needed by `Input.supports`.

`source_local_input` constructs all fields from the actual faithful action,
SQTK cover, F*=F and trivial two-core. There is no whole-module movement
hypothesis or starred-actor hypothesis on the restricted representation.
Source: Aschbacher–Smith D.2.14, pp.186–187, and 15.1.2, p.1084.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.BeforeMoved
open Subgroup Representation.BinaryOffender FittingConfigurations
open ElementaryCore.SupportExclusion Theory.GroupTheory
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

def movedModule (P : Subgroup G) [P.Normal] : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ ⊤ P
  apply_mem_toSubmodule g := fun _ hv =>
    (moved_stable ρ P ⊤ le_normalizer_of_normal (mem_top g) _).mpr hv

omit [Finite G] in
private theorem movedModule_fixed_map (P : Subgroup G) [P.Normal] (B : Subgroup G) :
    (fixedSpace (movedModule ρ P).toRepresentation B).map
      (movedModule ρ P).toSubmodule.subtype =
      subspaceCommutator ρ ⊤ P ⊓ fixedSpace ρ B := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.property, fun b => congrArg Subtype.val (hw b)⟩
  · intro hv
    exact ⟨⟨v,hv.1⟩,fun b => Subtype.ext (hv.2 b),rfl⟩

private theorem fixedSpace_split (P : Subgroup G) [P.Normal]
    (hodd : Odd (Nat.card P)) (B : Subgroup G) :
    (subspaceCommutator ρ ⊤ P ⊓ fixedSpace ρ B) ⊔
      (fixedSpace ρ P ⊓ fixedSpace ρ B) = fixedSpace ρ B := by
  let U := subspaceCommutator ρ ⊤ P
  let W := fixedSpace ρ P
  have hc := (moved_split ρ P hodd).symm
  have hU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
      le_normalizer_of_normal
  have hW := fixedSpace_stable_of_normal ρ P
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  intro v hv
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ W from hc.sup_eq_top ▸ Submodule.mem_top)
  have he (b : B) : (⟨ρ b u,(hU (mem_top b) u).2 hu⟩ : U) = ⟨u,hu⟩ ∧
      (⟨ρ b w,(hW (mem_top b) w).2 hw⟩ : W) = ⟨w,hw⟩ := by
    have hh := (U.prodEquivOfIsCompl W hc).injective
      (show (U.prodEquivOfIsCompl W hc)
          (⟨ρ b u,(hU (mem_top b) u).2 hu⟩,⟨ρ b w,(hW (mem_top b) w).2 hw⟩) =
        (U.prodEquivOfIsCompl W hc) (⟨u,hu⟩,⟨w,hw⟩) from
        (map_add (ρ b) u w).symm.trans (hv b))
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  exact Submodule.mem_sup.mpr ⟨u,⟨hu,fun b => congrArg Subtype.val (he b).1⟩,
    w,⟨hw,fun b => congrArg Subtype.val (he b).2⟩,rfl⟩

/-- Odd-core displacement of a fixed space is unchanged on the core's moved summand. -/
theorem movedModule_fixed_commutator_map (P : Subgroup G) [P.Normal]
    (hodd : Odd (Nat.card P)) (B D : Subgroup G) (hDP : D ≤ P) :
    (subspaceCommutator (movedModule ρ P).toRepresentation
      (fixedSpace (movedModule ρ P).toRepresentation B) D).map
        (movedModule ρ P).toSubmodule.subtype = subspaceCommutator ρ (fixedSpace ρ B) D := by
  let W := movedModule ρ P
  have he := subspaceCommutator_map_embedding ρ W.toRepresentation (MonoidHom.id G)
    W.toSubmodule.subtype (fun _ _ => rfl) D (fixedSpace W.toRepresentation B)
  simp only [Subgroup.map_id] at he
  rw [← he,movedModule_fixed_map]
  apply le_antisymm (subspaceCommutator_mono_left ρ inf_le_right D)
  apply Submodule.span_le.mpr
  rintro _ ⟨d,hd,v,hv,rfl⟩
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ (subspaceCommutator ρ ⊤ P ⊓ fixedSpace ρ B) ⊔
      (fixedSpace ρ P ⊓ fixedSpace ρ B) from (fixedSpace_split ρ P hodd B).symm ▸ hv)
  have hfix : ρ d w = w := hw.1 ⟨d,hDP hd⟩
  have heq : ρ d (u+w) - (u+w) = ρ d u-u := by rw [map_add,hfix]; abel
  rw [heq]
  exact Submodule.subset_span ⟨d,hd,u,hu,rfl⟩

/-- Faithfulness on a normal odd self-centralizing subgroup makes its moved action faithful. -/
theorem movedModule_faithful (hf : Function.Injective ρ)
    (P : Subgroup G) [P.Normal] (hodd : Odd (Nat.card P))
    (hself : centralizer (P : Set G) ≤ P) :
    Function.Injective (movedModule ρ P).toRepresentation := by
  let W := movedModule ρ P
  let N := W.toRepresentation.asGroupHom.ker
  have hn : N ⊓ P = ⊥ := by
    apply le_bot_iff.mp
    intro n hn
    apply (moved_faithful ρ hf P hodd).le
    refine ⟨hn.2,fun v hv => ?_⟩
    have hk : W.toRepresentation.asGroupHom n = 1 := hn.1
    have he := congrArg (fun k : (Module.End (ZMod 2) W.toSubmodule)ˣ => k.val (⟨v,hv⟩ : W.toSubmodule)) hk
    exact congrArg Subtype.val he
  have hc : N ≤ centralizer (P : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint (disjoint_iff.mpr hn))
  have hz : N = ⊥ := le_bot_iff.mp fun n hnN => hn.le ⟨hnN,hself (hc hnN)⟩
  have hi := (MonoidHom.ker_eq_bot_iff W.toRepresentation.asGroupHom).mp hz
  intro a b he
  apply hi
  apply Units.ext
  exact he

/-- The odd moved module is generated by its own core displacements. -/
theorem movedModule_full (P : Subgroup G) [P.Normal] (hodd : Odd (Nat.card P)) :
    subspaceCommutator (movedModule ρ P).toRepresentation ⊤ P = ⊤ := by
  let W := movedModule ρ P
  apply Submodule.map_injective_of_injective W.toSubmodule.subtype_injective
  have he := subspaceCommutator_map_embedding ρ W.toRepresentation
    (MonoidHom.id G) W.toSubmodule.subtype (fun _ _ => rfl) P ⊤
  simp only [Subgroup.map_id,Submodule.map_top,Submodule.range_subtype] at he ⊢
  rw [← he]
  exact NormalOddSeed.odd_moved_self ρ P hodd

variable [FiniteDimensional (ZMod 2) V]

/-- The original starred inequality transfers in the only equality case used by the geometry. -/
theorem strict_four_on_subrepresentation (W : Subrepresentation ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hcA : Nat.card A = 4)
    {B : Subgroup G} (hBA : B ≤ A) (hcB : Nat.card B = 2)
    (he : fixedCodim W.toRepresentation A = 4) :
    2 < fixedCodim W.toRepresentation B := by
  have hrA : rank A = 2 := by simp only [rank,hcA]; decide
  have hrB : rank B = 1 := by simp only [rank,hcB]; decide
  have hbound : fixedCodim ρ A ≤ 4 := by
    have hh := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
      (hA.1.2.2.2.trans_le hA.1.1)
    simpa only [hrA] using hh
  have hle := fixedCodim_subrepresentation_le ρ W A
  have hfour : fixedCodim ρ A = 4 := by omega
  have hs := (fixedCodim_subrepresentation_eq_iff ρ W A).mp (he.trans hfour.symm)
  have heB : fixedCodim W.toRepresentation B = fixedCodim ρ B := by
    apply (fixedCodim_subrepresentation_eq_iff ρ W B).mpr
    exact top_unique (hs.symm ▸ sup_le_sup_left (fixedSpace_antitone ρ hBA) _)
  have hne : B ≠ ⊥ := by intro hb; rw [hb,card_bot] at hcB; omega
  have hlt : B < A := lt_of_le_of_ne hBA (by intro hb; rw [hb,hcA] at hcB; omega)
  have hh := QhatStar.ratio_lt_of_lt ρ hA hlt hne
  rw [actionRatio,actionRatio,hrA,hrB,hfour,Nat.cast_one,div_one] at hh
  have hh' : (4 : ℝ≥0∞) < (fixedCodim ρ B : ℝ≥0∞) * 2 :=
    (ENNReal.div_lt_iff (by norm_num) (by norm_num)).mp hh
  have hn : 4 < fixedCodim ρ B * 2 := by exact_mod_cast hh'
  rw [heB]
  omega

/-- The actual original minimum actor supplies the weaker moved-module input. -/
theorem input_on_moved (hf : Function.Injective ρ)
    (P A : Subgroup G) [P.Normal] {s : ℕ}
    (hP : IsElementaryAbelian 3 P) (hcard : Nat.card P = 3 ^ s)
    (hs : s = 2 ∨ s = 3) (hAc : Nat.card A = 4) (hA : A ∈ QhatStar ρ)
    (hgen : P ⊔ A = ⊤) (hfaith : A ⊓ centralizer (P : Set G) = ⊥)
    (hfix : P ⊓ centralizer (A : Set G) = ⊥) (hcomm : ⁅P,A⁆ = P)
    (hhyper : ElementaryCore.HyperplaneSupport ρ P A) :
    Input (movedModule ρ P).toRepresentation P A s := by
  let : IsElementaryAbelian 3 P := hP
  let W := movedModule ρ P
  have hodd : Odd (Nat.card P) := hcard ▸ (by decide : Odd 3).pow
  have hself : centralizer (P : Set G) ≤ P := by
    intro g hg
    obtain ⟨p,hp,a,ha,rfl⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
    have hpC : p ∈ centralizer (P : Set G) := (Subgroup.le_centralizer P) hp
    have haC : a ∈ centralizer (P : Set G) := by
      simpa only [inv_mul_cancel_left] using
        (centralizer (P : Set G)).mul_mem ((centralizer (P : Set G)).inv_mem hpC) hg
    have ha1 : a = 1 := hfaith.le ⟨ha,haC⟩
    simpa only [ha1,mul_one] using hp
  refine ⟨movedModule_faithful ρ hf P hodd hself,inferInstance,hP,hcard,hs,hAc,
    hA.1.2.1,hgen,hfaith,hfix,hcomm,movedModule_full ρ P hodd,?_,?_,?_⟩
  · intro B hBA hr hn
    obtain ⟨hc,hd⟩ := hhyper B hBA hr hn
    refine ⟨hc,?_⟩
    let D := subspaceCommutator W.toRepresentation (fixedSpace W.toRepresentation B)
      (P ⊓ centralizer (B : Set G))
    calc
      Module.finrank (ZMod 2) D = Module.finrank (ZMod 2)
          (D.map W.toSubmodule.subtype) :=
        (Submodule.equivMapOfInjective W.toSubmodule.subtype W.toSubmodule.subtype_injective D).finrank_eq
      _ = 2 := by rw [movedModule_fixed_commutator_map ρ P hodd B _ inf_le_left]; exact hd
  · have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
      (hA.1.2.2.2.trans_le hA.1.1)
    have hr : rank A = 2 := by simp only [rank,hAc]; decide
    have hm := fixedCodim_subrepresentation_le ρ W A
    simp only [hr] at hb
    change fixedCodim W.toRepresentation A ≤ 4
    omega
  · exact fun B hBA hc he => strict_four_on_subrepresentation ρ W hA hAc hBA hc he

/-- Source D.2.14 constructs the local geometry on the literal moved module,
without assuming the original module is fully Fitting-moved. -/
theorem source_local_input
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥) :
    ∃ s : ℕ, Input (SourceReduction.localMoved ρ (pCore 3 G) A).toRepresentation
      ((pCore 3 G).subgroupOf (pCore 3 G ⊔ A)) (A.subgroupOf (pCore 3 G ⊔ A)) s := by
  let P := pCore 3 G
  let L := P ⊔ A
  let P₀ := P.subgroupOf L
  let A₀ := A.subgroupOf L
  let σ := ρ.comp L.subtype
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨hAc,hfix⟩ := SourceReduction.actor_four_and_common_centralizer ρ hH f honto hf hA hr hF hcore
  have hfaith := SourceReduction.actor_faithful_three ρ hf hA hr hF hcore
  have hsupport := source_lemma_D_2_14_hyperplaneSupport ρ hf hA hAc hfix
  obtain ⟨hElem,⟨s,hs,hcP,_⟩,hcomm⟩ :=
    ElementaryCore.elementary_structure_of_hyperplaneSupport ρ hf P A pCore_isPGroup
      hAc le_normalizer_of_normal hfaith hfix hsupport
  let : IsElementaryAbelian 3 P := hElem
  have hσ : Function.Injective σ := hf.comp L.subtype_injective
  have hstar : A₀ ∈ QhatStar σ := SourceReduction.starred_subgroupOf ρ hA le_sup_right
  have hcardA : Nat.card A₀ = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ L from le_sup_right)).toEquiv).trans hAc
  have hcore' : pCore 3 L = P₀ := SourceReduction.local_threeCore P A pCore_isPGroup
    (IsElementaryAbelian.isPGroup 2 A)
  have hfaith' : A₀ ⊓ centralizer (P₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    apply hfaith.le
    refine ⟨ha.1,?_⟩
    intro p hp
    exact congrArg Subtype.val (ha.2 ⟨p,(le_sup_left : P ≤ L) hp⟩ hp)
  have hfix' : P₀ ⊓ centralizer (A₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro p hp
    apply Subtype.ext
    apply hfix.le
    refine ⟨hp.1,?_⟩
    intro a ha
    exact congrArg Subtype.val (hp.2 ⟨a,(le_sup_right : A ≤ L) ha⟩ ha)
  have hcP₀ : Nat.card P₀ = 3 ^ s :=
    (Nat.card_congr (subgroupOfEquivOfLe (show P ≤ L from le_sup_left)).toEquiv).trans hcP
  have hgen : P₀ ⊔ A₀ = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hcomm' : ⁅P₀,A₀⁆ = P₀ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,hcomm]
  have hhyper : ElementaryCore.HyperplaneSupport σ P₀ A₀ := by
    have hh := source_lemma_D_2_14_hyperplaneSupport σ hσ hstar hcardA (hcore'.symm ▸ hfix')
    rw [hcore'] at hh
    exact hh
  have hinput := input_on_moved σ hσ P₀ A₀ (IsElementaryAbelian.subgroupOf le_sup_left)
    hcP₀ hs hcardA hstar hgen hfaith' hfix' hcomm' hhyper
  have hspace : subspaceCommutator σ ⊤ P₀ = subspaceCommutator ρ ⊤ P := by
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le le_sup_left]
  -- The two representations use the same inclusion into the original V.
  have hW : movedModule σ P₀ = SourceReduction.localMoved ρ P A := by
    apply Subrepresentation.toSubmodule_injective
    exact hspace
  refine ⟨s,?_⟩
  rw [hW] at hinput
  exact hinput

end CFSG.Quasithin.ChapterD.BeforeMoved
