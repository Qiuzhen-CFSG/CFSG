module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
/-!
# Conjugation exchanges the original marked A₅ coordinates

The square of any Sylow element stabilizes L, since its stabilizer has index
two. Its induced A₅ automorphism accounts for the first coordinate when t
exchanges the factors. The equality is verified on L and tLt⁻¹ and extends
through their literal join L₀. No order-two hypothesis on t is used.

Source: Aschbacher–Smith D.3.6–7 and10.1.1, pp.196–199 and741.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Conjugation by t as an automorphism of the literal orbit. -/
def originalOrbitConjugation {t : G} (ht : t ∈ (T : Subgroup G)) :
    MulAut (localOrbit T L) :=
  ((MulAut.conj t).subgroupMap (localOrbit T L)).trans
    (MulEquiv.subgroupCongr
      (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)))

/-- The original factor automorphism induced by t². -/
noncomputable def originalSquareConjugation
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) : MulAut L :=
  ((MulAut.conj (t*t)).subgroupMap L).trans (MulEquiv.subgroupCongr (by
    apply mem_normalizer_iff_map_conj_eq.mp
    exact mul_self_mem_of_index_two
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      (⟨t,ht⟩ : (T : Subgroup G))))

/-- The quotient automorphism induced by t² in the prescribed A₅ marking. -/
noncomputable def originalA5ConjugationTwist
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) : MulAut (alternatingGroup (Fin 5)) :=
  e.symm.trans ((QuotientGroup.congr _ _ (originalSquareConjugation D hn ht)
    (pCore_map_iso 2 (originalSquareConjugation D hn ht))).trans e)

/-- Exact exchange of the marked product coordinates under the original t. -/
theorem originalA5ProductProjection_conjugate (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (x : localOrbit T L) :
    originalA5ProductProjection D e hn ht htn (originalOrbitConjugation ht x) =
      (originalA5ConjugationTwist D e hn ht (originalA5ProductProjection D e hn ht htn x).2,
        (originalA5ProductProjection D e hn ht htn x).1) := by
  let R := localOrbit T L
  let A := L.subgroupOf R
  let B := (L.map (MulAut.conj t).toMonoidHom).subgroupOf R
  let q := originalA5ProductProjection D e hn ht htn
  let τ := originalOrbitConjugation (L := L) ht
  let β := originalA5ConjugationTwist D e hn ht
  let f := q.comp τ.toMonoidHom
  let g := ((β.toMonoidHom.comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)).comp q
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    rw [←subgroupOf_sup (le_componentOrbit L T) (le_sup_right.trans hp.le),hp,subgroupOf_self]
  have hA : A ≤ f.eqLocus g := by
    intro a ha
    let l : L := ⟨a,ha⟩
    change q (τ a) = (β (q a).2,(q a).1)
    have hfirst : q a = (e (QuotientGroup.mk' _ l),1) :=
      originalA5ProductProjection_first D e hn ht htn l
    have hsecond : q (τ a) = (1,e (QuotientGroup.mk' _ l)) :=
      originalA5ProductProjection_second D e hn ht htn l
    rw [hfirst,hsecond]
    exact Prod.ext β.map_one.symm rfl
  have hB : B ≤ f.eqLocus g := by
    intro b hb
    obtain ⟨l,hl,he⟩ := mem_map.mp hb
    let l' : L := ⟨l,hl⟩
    have hb' : b = originalConjugateOrbitInclusion ht l' := Subtype.ext he.symm
    subst b
    change q (τ (originalConjugateOrbitInclusion ht l')) =
      (β (q (originalConjugateOrbitInclusion ht l')).2,
        (q (originalConjugateOrbitInclusion ht l')).1)
    rw [show q (originalConjugateOrbitInclusion ht l') = (1,e (QuotientGroup.mk' _ l')) from
      originalA5ProductProjection_second D e hn ht htn l']
    let l₂ := originalSquareConjugation D hn ht l'
    have he₂ : τ (originalConjugateOrbitInclusion ht l') =
        (⟨l₂,le_componentOrbit L T l₂.property⟩ : R) := by
      apply Subtype.ext
      change t * (t * l * t⁻¹) * t⁻¹ = (t*t) * l * (t*t)⁻¹
      simp only [mul_inv_rev,mul_assoc]
    rw [he₂]
    change q ⟨l₂,le_componentOrbit L T l₂.property⟩ = (β (e (QuotientGroup.mk' _ l')),1)
    rw [show q ⟨l₂,le_componentOrbit L T l₂.property⟩ = (e (QuotientGroup.mk' _ l₂),1) from
      originalA5ProductProjection_first D e hn ht htn l₂]
    congr 1
    change e (QuotientGroup.mk' _ l₂) =
      e ((QuotientGroup.congr _ _ (originalSquareConjugation D hn ht)
        (pCore_map_iso 2 (originalSquareConjugation D hn ht))) (e.symm (e (QuotientGroup.mk' _ l'))))
    rw [e.symm_apply_apply]
    rfl
  exact (sup_le hA hB) (hgen.symm ▸ mem_top x)
end CFSG.Quasithin.Chapter10
