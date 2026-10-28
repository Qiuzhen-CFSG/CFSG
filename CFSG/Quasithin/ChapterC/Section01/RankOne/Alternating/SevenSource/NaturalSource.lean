module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalThompsonBaumann
public import Theory.Representation.BinaryPermutationMulAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# C.1.24(a) from the original natural seven-letter module

The original centralizer quotient and module action determine the Thompson
and Baumann images. In the centralizing branch, B.2.10 makes Baum(T) normal;
its nontriviality follows from the original module commutator. In the moving
branch, the stable-family calculation marks both images as the three-swap
eight-group. Conjugating the quotient marking and natural embedding together
retains their equivariance. B.2.10 then supplies the literal kernel Sylow and
two-core intersection required by the cubic seed and its block propagation.

The natural submodule embedding and fixed-codimension comparison are the
module data supplied by the preceding B.5 reduction. No Thompson-image,
Baumann-image, kernel-Sylow or short-block premise remains.

Source: Aschbacher–Smith C.1.24(a), printed pp.130–131, specialized to R = T
and the natural S₇ branch of the module classification.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
open SymmetricSix BinaryPermutation
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
variable {G : Type*} [Group G] [Finite G]

theorem symmetric_seven_twoCore_eq_bot : pCore 2 (Equiv.Perm (Fin 7)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Equiv.Perm (Fin 7))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 7)) hnt
  have hdiv : 2520 ∣ Nat.card (pCore 2 (Equiv.Perm (Fin 7))) := by
    have hc : Nat.card (alternatingGroup (Fin 7))=2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]; decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 7))).exists_card_eq
  have ht : 3 ∣ 2^n := hn ▸ dvd_trans (by decide : 3 ∣ 2520) hdiv
  exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow ht)

/-- The original natural S₇ branch, before choosing the pair marking. -/
theorem normal_characteristic_or_block_of_natural_seven
    (L V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L) (T : Sylow 2 G)
    (hprod : ∀ g:G,∃l∈L,∃t∈(T:Subgroup G),l*t=g)
    (q : G →* Sym) (hq : Function.Surjective q)
    (hk : q.ker=centralizer (V : Set G))
    (hLq : L.map q=alternatingGroup (Fin 7))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (naturalRepresentation (Fin 7)) A)
    (f : Multiplicative (natural (Fin 7)) →* V) (hfV : Function.Injective f)
    (he : ∀ (g : G) (v : natural (Fin 7)),
      f (Multiplicative.ofAdd (naturalRepresentation (Fin 7) (q g) v)) =
        MulAut.conjNormal g (f (Multiplicative.ofAdd v)))
    (hm : ⁅V,L⁆ ≠ ⊥) :
    (∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann (T : Subgroup G)).subtype).Normal) ∨ IsBlock L := by
  have hQT : pCore 2 G ≤ T := pCore_isPGroup.le_sylow_of_normal T
  have hVT : V ≤ T := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩).trans hQT
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker
  · have hdata := ChapterB.lemma_B_2_10_two V (T : Subgroup G) q hq hk T hQT le_rfl
      symmetric_seven_twoCore_eq_bot L (Or.inl ⟨hL,inferInstance⟩) hm hprod
    have hn := (ChapterB.lemma_B_2_10_centralizing V (T : Subgroup G) hVT hQT
      hdata.2.1 (by simpa only [ChapterB.thompsonJ_zero,hk] using hJ)).2.2.2
    have hTne : (T : Subgroup G) ≠ ⊥ := by
      intro ht
      have hv : V=⊥ := le_bot_iff.mp (hVT.trans_eq ht)
      exact hm (by rw [hv,commutator_bot_left])
    let : Nontrivial (ChapterB.baumann (T : Subgroup G)) :=
      (nontrivial_iff_ne_bot _).mpr (baumann_ne_bot (T : Subgroup G) T.isPGroup' hTne)
    exact Or.inl ⟨⊤,inferInstance,top_ne_bot,by
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hn⟩
  let fadd : natural (Fin 7) →+ Additive V := {
    toFun v := Additive.ofMul (f (Multiplicative.ofAdd v))
    map_zero' := map_one f
    map_add' v w := map_mul f (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) }
  let s := fadd.toZModLinearMap 2
  have hsi : Function.Injective s := by
    intro v w h
    exact congrArg Multiplicative.toAdd (hfV (congrArg Additive.toMul h))
  have hse : ∀ g v, s (naturalRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation V q hq hk g (s v) := by
    intro g v
    obtain ⟨x,rfl⟩ := hq g
    apply Additive.toMul.injective
    apply Subtype.ext
    change (f (Multiplicative.ofAdd (naturalRepresentation (Fin 7) (q x) v)) : G) = _
    rw [NormalElementaryQuotient.representation_apply]
    exact congrArg (fun u : V => (u:G)) (he x v)
  obtain ⟨a,hJa,hSa,_⟩ :=
    Alternating.SevenSource.natural_thompson_baumann_images_of_natural_coordinates
      V T hVT q hq hk hc hJ s hsi hse
  let q' := (MulAut.conj a⁻¹).toMonoidHom.comp q
  have hq' : Function.Surjective q' := (MulAut.conj a⁻¹).surjective.comp hq
  have hk' : q'.ker=centralizer (V : Set G) :=
    (MonoidHom.ker_comp_of_injective q (MulAut.conj a⁻¹).toMonoidHom
      (MulAut.conj a⁻¹).injective).trans hk
  have hLq' : L.map q'=alternatingGroup (Fin 7) := by
    rw [show L.map q'=(L.map q).map (MulAut.conj a⁻¹).toMonoidHom from (map_map _ _ _).symm,hLq]
    apply eq_of_le_of_card_ge
    · rintro _ ⟨g,hg,rfl⟩
      exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem g hg a⁻¹
    · rw [card_map_of_injective (MulAut.conj a⁻¹).injective]
  have hcancel (A : Subgroup Sym) :
      (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom=A := by
    exact A.conjBy_inv a
  have hJ' : (elementaryAbelianMaxJ (T : Subgroup G)).map q'=pairElementary := by
    rw [show (elementaryAbelianMaxJ (T : Subgroup G)).map q'=
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q).map (MulAut.conj a⁻¹).toMonoidHom from
        (map_map _ _ _).symm,hJa,hcancel]
  have hS' : (ChapterB.baumann (T : Subgroup G)).map q'=pairElementary := by
    rw [show (ChapterB.baumann (T : Subgroup G)).map q'=
      ((ChapterB.baumann (T : Subgroup G)).map q).map (MulAut.conj a⁻¹).toMonoidHom from
        (map_map _ _ _).symm,hSa,hcancel]
  let f' := f.comp (naturalMulAction (Fin 7) a).toMonoidHom
  have hf' : Function.Injective f' := hfV.comp (naturalMulAction (Fin 7) a).injective
  have he' : ∀ (g : G) (v : natural (Fin 7)),
      f' (Multiplicative.ofAdd (naturalRepresentation (Fin 7) (q' g) v)) =
        MulAut.conjNormal g (f' (Multiplicative.ofAdd v)) := by
    intro g v
    change f (Multiplicative.ofAdd (naturalRepresentation (Fin 7) a
      (naturalRepresentation (Fin 7) (a⁻¹*q g*a) v))) = _
    rw [←Module.End.mul_apply,←map_mul]
    rw [show a*(a⁻¹*q g*a)=q g*a from by group]
    rw [map_mul,Module.End.mul_apply,he]
    rfl
  have hdata := ChapterB.lemma_B_2_10_two V (T : Subgroup G) q' hq' hk' T hQT le_rfl
    symmetric_seven_twoCore_eq_bot L (Or.inl ⟨hL,inferInstance⟩) hm hprod
  have hcore : (T : Subgroup G) ⊓ q'.ker=pCore 2 G := by
    simpa only [hk'] using hdata.2.1.symm
  obtain ⟨P,hPn,hP⟩ : ∃ P : Sylow 2 q'.ker, (P : Subgroup q'.ker).Normal ∧
      (P : Subgroup q'.ker).map q'.ker.subtype=pCore 2 G := by
    rw [hk']
    exact hdata.1
  exact normal_characteristic_or_block_of_marked_natural_seven L V hL hf hfL T hprod
    q' hq' hLq' f' hf' he' P hP hcore hJ' hS'

/-- Linear-coordinate interface for the natural submodule delivered by B.5. -/
theorem normal_characteristic_or_block_of_natural_seven_linear
    (L V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L) (T : Sylow 2 G)
    (hprod : ∀ g:G,∃l∈L,∃t∈(T:Subgroup G),l*t=g)
    (q : G →* Sym) (hq : Function.Surjective q)
    (hk : q.ker=centralizer (V : Set G))
    (hLq : L.map q=alternatingGroup (Fin 7))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (naturalRepresentation (Fin 7)) A)
    (s : natural (Fin 7) →ₗ[ZMod 2] Additive V) (hs : Function.Injective s)
    (he : ∀ g v, s (naturalRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation V q hq hk g (s v))
    (hm : ⁅V,L⁆ ≠ ⊥) :
    (∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann (T : Subgroup G)).subtype).Normal) ∨ IsBlock L := by
  apply normal_characteristic_or_block_of_natural_seven L V hL hf hfL T hprod
    q hq hk hLq hc s.toAddMonoidHom.toMultiplicativeLeft
    (fun v w h => Multiplicative.toAdd.injective (hs (congrArg Additive.ofMul h)))
    (fun g v => ?_) hm
  apply Subtype.ext
  change ((s (naturalRepresentation (Fin 7) (q g) v)).toMul : G) =
    g * ((s v).toMul : G) * g⁻¹
  rw [he,NormalElementaryQuotient.representation_apply]
end CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
