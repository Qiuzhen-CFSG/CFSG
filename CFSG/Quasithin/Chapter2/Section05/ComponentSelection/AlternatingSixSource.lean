module
public import Theory.SpecificGroups.AlternatingSix.CentralOuterLocal
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.SymmetricFourSubgroup
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlternatingSevenSource
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
/-! Exclude the original outer-transposition actions on A6 and triple A6
when Gamma-even is empty. The normalizer of the original component Sylow
acts through the checked Aut(A6) holomorph. Its central marked involution
preserves an escaping S4; the characteristic odd-cover lift belongs to He
and is forced into M by the component-orbit argument. The fixed S4 also
lifts into C_G(z), hence into M. Maximality of this S4 forces the quotient
image of M intersect L to be all A6, and perfectness lifts that containment
to L, contradicting the original local setup. No global component normality
or Dynkin-action assertion is assumed.
Source: Aschbacher--Smith 2.5.2, printed p.551, applied to 1.1.5(3)(c). -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open AlternatingSix.ShadowLocal Sporadic.Mathieu.M22ValueBound.OddCoverLifting
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem alternating_six_outer_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : (L ⧸ center L) ≃* A6)
    (ho : Odd (Nat.card (center L))) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (ha : ∀ x : L, (e (QuotientGroup.mk' (center L) (α x)) : Equiv.Perm (Fin 6)) =
      σ * e (QuotientGroup.mk' (center L) x) * σ⁻¹) : False := by
  let q : L →* A6 := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hqo : Odd (Nat.card q.ker) := hker.symm ▸ ho
  let φ := (MulAut.congr e).toMonoidHom.comp (center L).quotientAut
  have compat (a : MulAut L) (x : L) : q (a x) = φ a (q x) := by
    change e (QuotientGroup.mk' (center L) (a x)) =
      e ((center L).quotientAut a (e.symm (e (QuotientGroup.mk' (center L) x))))
    rw [e.symm_apply_apply,quotientAut_apply_mk]
  have hφα : φ α = permutationAction σ := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := hq y
    rw [← compat]
    exact Subtype.ext (ha x)
  let A : Subgroup G := (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G)
  let η : A →* MulAut L := L.normalizerMonoidHom.comp (inclusion inf_le_right)
  let ρ : A →* AutA6 := φ.comp η
  have hA : IsPGroup 2 A := (S.isPGroup'.map H.subtype).to_le inf_le_left
  let az : A := ⟨z,h.mem_sylow,h.normalizes⟩
  have hηz : η az=α := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (hα x).symm
  have hρz : ρ az=permutationAction σ := by
    change φ (η az)=_
    rw [hηz,hφα]
  have hcentral (a : A) : ρ a * permutationAction σ = permutationAction σ * ρ a := by
    rw [← hρz,← map_mul,← map_mul]
    exact congrArg ρ (Subtype.ext (h.central a a.property.1))
  obtain ⟨P,hP⟩ := h.component_sylow
  let R := P.mapSurjective (f := q) hq
  have hR : (R : Subgroup A6).map (MulAut.conj : A6 →* AutA6) ≤ ρ.range := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    have hxS : (x : G) ∈ (S : Subgroup H).map H.subtype := by
      change x ∈ ((S : Subgroup H).map H.subtype).subgroupOf L
      rwa [← hP]
    let ax : A := ⟨x,hxS,L.le_normalizer x.property⟩
    refine ⟨ax,?_⟩
    have hηx : η ax=MulAut.conj x := by ext y;rfl
    change φ (η ax)=MulAut.conj (q x)
    rw [hηx]
    apply MulEquiv.ext
    intro y
    obtain ⟨v,rfl⟩ := hq y
    rw [← compat]
    change q (x*v*x⁻¹)=q x*q v*(q x)⁻¹
    simp only [map_mul,map_inv]
  obtain ⟨U,⟨eU⟩,hUinv,hUescape⟩ := CentralOuterLocal.exists_invariant_local_of_action
    ρ hA R hR σ hσ ⟨az,hρz⟩ hcentral
  obtain ⟨K,⟨eK⟩,hKmap,_,hKinv⟩ := exists_invariant_symmetric_four_lift q hq
    hker.le hqo U eU
  have hKM : K ≤ M.subgroupOf L := by
    let V := K.map L.subtype
    have hV : V ∈ Chapter1.He G := by
      apply Chapter1.mem_He_iff.mpr
      exact (Theory.Quasithin.centralizer_pCore_le_iff 2
        (K.equivMapOfInjective L.subtype L.subtype_injective)).mp
        (Matrix.PSL3Two.ParabolicCoreModel.core_selfCentralizing eK)
    have hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G) := by
      intro s hs
      let a : A := ⟨s,hs⟩
      have hk := hKinv (η a) (ρ a) (compat (η a)) (hUinv a)
      apply mem_normalizer_iff_map_conj_eq.mpr
      have he : (MulAut.conj s).toMonoidHom.comp L.subtype = L.subtype.comp (η a).toMonoidHom := by ext x;rfl
      change (K.map L.subtype).map (MulAut.conj s).toMonoidHom=K.map L.subtype
      rw [map_map,he,← map_map,hk]
    have hVM := component_invariant_local_le hH hempty S h.sylow_le h.component
      h.component_le (map_subtype_le K) hV hinv
    intro x hx
    exact hVM (mem_map_of_mem L.subtype hx)
  let B := GLS3.Chapter5.automorphismFixedSubgroup (permutationAction σ)
  obtain ⟨eB⟩ := swap_fixed_equiv_symmetricFour σ hσ
  obtain ⟨J,_,hJmap,hJinj,hJinv⟩ := exists_invariant_symmetric_four_lift q hq
    hker.le hqo B eB
  have hBmap : B.map (permutationAction σ).toMonoidHom=B := by
    apply eq_of_le_of_card_ge ?_ (card_map_of_injective (permutationAction σ).injective).ge
    rintro _ ⟨x,hx,rfl⟩
    change permutationAction σ x ∈ B
    rw [show permutationAction σ x=x from hx]
    exact hx
  have hJα : J.map α.toMonoidHom=J := hJinv α (φ α) (compat α) (hφα.symm ▸ hBmap)
  have hJM : J ≤ M.subgroupOf L := by
    intro x hx
    apply h.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hax : α x=x := by
      have hxB : q x ∈ B := hJmap ▸ mem_map_of_mem q hx
      have hh : q (α x)=q x := by rw [compat,hφα]; exact hxB
      exact congrArg Subtype.val (hJinj (show (q.comp J.subtype) ⟨α x,hJα ▸ mem_map_of_mem α.toMonoidHom hx⟩ =
        (q.comp J.subtype) ⟨x,hx⟩ from hh))
    have hh := (hα x).symm.trans (congrArg Subtype.val hax)
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let Y := (M.subgroupOf L).map q
  have hBY : B ≤ Y := by rw [← hJmap]; exact map_mono hJM
  have hUY : U ≤ Y := by rw [← hKmap]; exact map_mono hKM
  have hY : Y=⊤ := by
    apply (CentralOuterLocal.symmetric_four_isCoatom B eB).2
    apply lt_of_le_of_ne hBY
    intro he
    exact hUescape (fun x hx => (he ▸ hUY hx : x ∈ B))
  let := h.quasisimple
  have htop : (⊤ : Subgroup L) ≤ M.subgroupOf L :=
    perfect_le_of_map_le_of_central_kernel q hker.le ⊤ (M.subgroupOf L) (by change _ ≤ Y; rw [hY]; exact le_top)
  exact h.outside (fun x hx => htop (show (⟨x,hx⟩ : L) ∈ ⊤ from mem_top _))

open Chapter15.Section03.Candidates.ComponentStructure

theorem alternating_six_action_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (ha : AlternatingAction α 6 σ) : False := by
  rcases ha with ⟨e,ha⟩ | ⟨_,⟨ec⟩,e,ha⟩
  · have hc : Nat.card (center L) = 1 := by
      rw [Nat.card_congr (centerCongr e).toEquiv,
        alternatingGroup.center_eq_bot (by simp)]
      exact card_bot
    let f : (L ⧸ center L) ≃* A6 :=
      ((QuotientGroup.quotientMulEquivOfEq ((eq_bot_iff_card _).mpr hc)).trans
        QuotientGroup.quotientBot).trans e
    exact alternating_six_outer_false hH hempty h f (hc ▸ (by decide)) α hα σ hσ ha
  · have hc : Nat.card (center L) = 3 := by
      rw [Nat.card_congr ec.toEquiv]
      simp
    exact alternating_six_outer_false hH hempty h e (hc ▸ (by decide)) α hα σ hσ ha

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
