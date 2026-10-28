module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.CubicAction
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Source
/-!
# The reduced A₃ Baumann Sylow subgroup

The actual binary-plane action is onto SL₂(2). Its projection is the full
four-element module, and its residual fixed space is zero by the original
A₃ block structure. Applying the checked natural Baumann theorem preserves
the literal KT action and proves the full Sylow image and Sylow placement.

Source: Aschbacher–Smith C.5.4(2), printed p.155.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem cubic_reduced_action_and_sylow (h : Setup R K F) (hA : IsAlternatingBlock K 3)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) (hST : S R ≤ T)
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥) :
    ∃ (e : U K ≃* Multiplicative (Fin 2 → ZMod 2))
      (q : (K ⊔ T : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      Function.Surjective q ∧
      q.ker = (centralizer (U K : Set G)).subgroupOf (K ⊔ T) ∧
      (∀ z u, e (normalizerConjugate (inclusion (sup_le K.le_normalizer hn) z) u) =
        cubicNaturalAction (q z) (e u)) ∧
      ((S T).subgroupOf (K ⊔ T)).map q = (T.subgroupOf (K ⊔ T)).map q ∧
      Chapter1.IsSylowIn 2 (S T) (K ⊔ S T) := by
  obtain ⟨e,q,hq,hker,he⟩ := cubic_reduced_action h hA T hT hn hST
  let A := K ⊔ T
  let V := (U K).subgroupOf A
  have hUA : U K ≤ A := (map_subtype_le _).trans le_sup_left
  let : V.Normal := reduced_module_normal K T hn
  let : IsElementaryAbelian 2 V := reduced_module_elementary K T hA.2.1
  have hker' : q.ker = centralizer (V : Set A) := by
    rw [native_centralizer A (U K) hUA]
    exact hker
  let eV : V ≃* U K := subgroupOfEquivOfLe hUA
  let f := (e.toMonoidHom.comp eV.toMonoidHom).toAdditiveLeft.toZModLinearMap 2
  have hf : Function.Bijective f := e.bijective.comp eV.bijective
  let ρ := NormalElementaryQuotient.representation V q hq hker'
  have he' : ∀ g v, f (ρ g v) = SL2NaturalOffenders.NoStrong.natural g (f v) := by
    intro g v
    obtain ⟨z,rfl⟩ := hq g
    have hv := NormalElementaryQuotient.representation_apply V q hq hker' z v
    have heV : eV (ρ (q z) v).toMul =
        normalizerConjugate (inclusion (sup_le K.le_normalizer hn) z) (eV v.toMul) := by
      apply Subtype.ext
      exact congrArg (fun z : A => (z : G)) hv
    change (e (eV (ρ (q z) v).toMul)).toAdd = _
    rw [heV,he]
    rfl
  have hres := normal_extension_residual K T hA.2.1.twoPerfect hT hn
  have hk : f.ker = fixedSpace ρ ((pResidual 2 A).map q) := by
    apply le_antisymm
    · intro v hv
      have hz : v = 0 := hf.1 (hv.trans (map_zero f).symm)
      exact hz ▸ Submodule.zero_mem _
    · intro v hv
      have hc := (NormalElementaryQuotient.mem_fixedSpace_image V q hq hker' (pResidual 2 A) v).mp hv
      have hcK : (eV v.toMul : G) ∈ centralizer (K : Set G) := by
        intro k hk
        obtain ⟨z,hz,rfl⟩ := (hres.symm ▸ hk : k ∈ (pResidual 2 A).map A.subtype)
        exact congrArg (fun z : A => (z : G)) (hc z hz)
      have hz : v = 0 := Additive.toMul.injective (eV.map_eq_one_iff.mp (cubic_module_fixed_eq_one hA (eV v.toMul) hcK))
      exact hz ▸ Submodule.zero_mem _
  have hred := reduced_module_reduced K T hA.2.1 hT hn
  have hJ := native_thompson_moves K T hA.2.1 hT hn P hP hno
  have hs := (ChapterB.RankOneBaumann.natural_baumann_sylow_and_alpha P hmin V hred hJ q hq hker' f hf.2 he' hk).1
  have hi := (ChapterB.RankOneBaumann.thompson_baumann_images_of_natural_quotient P V q hq hker'
    (hred.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hJ f hf.2 he').2
  have hB : (ChapterB.baumann (P : Subgroup A)).map A.subtype = S T :=
    (show (ChapterB.baumann (P : Subgroup A)).map A.subtype =
      ChapterB.baumann ((P : Subgroup A).map A.subtype) from
      baumann_map_injective A.subtype A.subtype_injective (P : Subgroup A)).trans (congrArg ChapterB.baumann hP)
  have hb : ChapterB.baumann (P : Subgroup A) = (S T).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hB,map_subgroupOf_eq_of_le (show S T ≤ A from inf_le_left.trans le_sup_right)]
  have hPi : (P : Subgroup A) = T.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show T ≤ A from le_sup_right)]
  have hm := (Chapter1.IsSylowIn.map_iff A.subtype A.subtype_injective).mpr hs
  rw [Subgroup.map_sup,hres,hB] at hm
  rw [hb,hPi] at hi
  exact ⟨e,q,hq,hker,he,hi,hm⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
