module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.ActionSwap
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.OuterActor
/-!
# The original source actors in paired coordinates

The actor `x` preserves both components, so conjugation in the chosen product
coordinates is the product of the transported component automorphisms. The
source four-group argument makes each restriction outer. The exchange actor
`s` has the swapped product form supplied by `ActionSwap`.

These are the literal actions induced from the source subgroup and its chosen
component coordinates; no replacement of the original actors is used here.

Source: Aschbacher–Smith, Lemma 2.4.34, printed p.548, the identification of the
generated group with its action on the two commuting components.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
open Subgroup
private theorem transported_pair_action {G F : Type*} [Group G] [Group F]
    (K L J : Subgroup G) (hK : K ≤ J) (hL : L ≤ J)
    (eK : K ≃* F) (eL : L ≃* F) (e : J ≃* F × F)
    (hleft : ∀ k : K, e (inclusion hK k) = (eK k,1))
    (hright : ∀ l : L, e (inclusion hL l) = (1,eL l))
    (x : G) (hxK : x ∈ normalizer (K : Set G))
    (hxL : x ∈ normalizer (L : Set G)) (hxJ : x ∈ normalizer (J : Set G)) :
    MulAut.congr e (J.normalizerMonoidHom ⟨x,hxJ⟩) =
      (MulAut.congr eK (K.normalizerMonoidHom ⟨x,hxK⟩)).prodCongr
        (MulAut.congr eL (L.normalizerMonoidHom ⟨x,hxL⟩)) := by
  let f := MulAut.congr e (J.normalizerMonoidHom ⟨x,hxJ⟩)
  let a := MulAut.congr eK (K.normalizerMonoidHom ⟨x,hxK⟩)
  let b := MulAut.congr eL (L.normalizerMonoidHom ⟨x,hxL⟩)
  have hfleft (k : K) : f (eK k,1) = (a (eK k),1) := by
    rw [← hleft k]
    change e (J.normalizerMonoidHom ⟨x,hxJ⟩ (e.symm (e (inclusion hK k)))) = _
    rw [e.symm_apply_apply]
    have hin : J.normalizerMonoidHom ⟨x,hxJ⟩ (inclusion hK k) =
        inclusion hK (K.normalizerMonoidHom ⟨x,hxK⟩ k) := rfl
    rw [hin,hleft]
    change (eK (K.normalizerMonoidHom ⟨x,hxK⟩ k),1) =
      (eK (K.normalizerMonoidHom ⟨x,hxK⟩ (eK.symm (eK k))),1)
    rw [eK.symm_apply_apply]
  have hfright (l : L) : f (1,eL l) = (1,b (eL l)) := by
    rw [← hright l]
    change e (J.normalizerMonoidHom ⟨x,hxJ⟩ (e.symm (e (inclusion hL l)))) = _
    rw [e.symm_apply_apply]
    have hin : J.normalizerMonoidHom ⟨x,hxJ⟩ (inclusion hL l) =
        inclusion hL (L.normalizerMonoidHom ⟨x,hxL⟩ l) := rfl
    rw [hin,hright]
    change (1,eL (L.normalizerMonoidHom ⟨x,hxL⟩ l)) =
      (1,eL (L.normalizerMonoidHom ⟨x,hxL⟩ (eL.symm (eL l))))
    rw [eL.symm_apply_apply]
  apply MulEquiv.ext
  rintro ⟨u,v⟩
  obtain ⟨k,rfl⟩ := eK.surjective u
  obtain ⟨l,rfl⟩ := eL.surjective v
  change f (eK k,eL l) = (a (eK k),b (eL l))
  calc
    f (eK k,eL l) = f ((eK k,1)*(1,eL l)) := by simp only [Prod.mk_mul_mk,mul_one,one_mul]
    _ = (a (eK k),b (eL l)) := by rw [map_mul,hfleft,hfright]; simp


private theorem transported_not_inner {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) (ha : a ∉ MulAut.innerSubgroup A) :
    ∀ b : B, MulAut.congr e a ≠ MulAut.conj b := by
  intro b hb
  obtain ⟨u, hu⟩ := (MulAut.congr_inner_iff e a).mp ⟨b,hb⟩
  exact ha ⟨u,hu.symm⟩

open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G}

/-- The original factor-preserving actor is outer in each of the chosen coordinates. -/
theorem source_x_action_normal_form
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (hE : K = (componentLayer (centralizer ({g.z₂} : Set G))).map
      (centralizer ({g.z₂} : Set G)).subtype)
    (ho : pPrimeCore 2 (centralizer ({g.z₂} : Set G)) = ⊥)
    (hfirst : d.block.map d.H.subtype ≤ K)
    (hcomm : c.U₂ ≤ centralizer (K : Set G)) (eK : K ≃* Matrix.PSL3Two.SL) :
    let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
    let J := K ⊔ Ks
    let I := J ⊔ (T : Subgroup G)
    let eS := K.equivMapOfInjective (MulAut.conj c.s⁻¹).toMonoidHom (MulAut.conj c.s⁻¹).injective
    ∀ (eJ : J ≃* Matrix.PSL3Two.SL × Matrix.PSL3Two.SL),
      (∀ k : K, eJ (inclusion le_sup_left k) = (eK k,1)) →
      (∀ k : K, eJ (inclusion le_sup_right (eS k)) = (1,eK k)) →
      ∀ hn : I ≤ normalizer (J : Set G),
        let ρ := (MulAut.congr eJ).toMonoidHom.comp
          (J.normalizerMonoidHom.comp (inclusion hn))
        let xI : I := ⟨c.x, Subgroup.mem_sup_right c.x_mem⟩
        ∃ a b : MulAut Matrix.PSL3Two.SL, ρ xI = a.prodCongr b ∧
          (∀ u : Matrix.PSL3Two.SL, a ≠ MulAut.conj u) ∧
          (∀ v : Matrix.PSL3Two.SL, b ≠ MulAut.conj v) := by
  intro Ks J I eS eJ hleft hright hn ρ xI
  have hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (K ≃* Matrix.PSL3Two.PSL) :=
    Or.inr ⟨eK.trans Matrix.PSL3Two.equiv⟩
  obtain ⟨hxK,hxKs,houtK,houtKs⟩ :=
    source_x_outer hG hu c g K hK hE ho hfirst hmodel hcomm
  let e₂ : Ks ≃* Matrix.PSL3Two.SL := eS.symm.trans eK
  have hright' (k : Ks) : eJ (inclusion le_sup_right k) = (1,e₂ k) := by
    obtain ⟨k,rfl⟩ := eS.surjective k
    simpa only [e₂, MulEquiv.trans_apply, eS.symm_apply_apply] using hright k
  refine ⟨MulAut.congr eK (K.normalizerMonoidHom ⟨c.x,hxK⟩),
    MulAut.congr e₂ (Ks.normalizerMonoidHom ⟨c.x,hxKs⟩), ?_,
    transported_not_inner eK _ houtK, transported_not_inner e₂ _ houtKs⟩
  exact transported_pair_action K Ks J le_sup_left le_sup_right eK e₂ eJ hleft hright'
    c.x hxK hxKs (hn xI.property)
end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
