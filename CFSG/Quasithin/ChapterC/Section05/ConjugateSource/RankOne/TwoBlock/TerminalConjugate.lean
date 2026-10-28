module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.TerminalCentralization

/-!
# The conjugate full centralizer has the same central factor

Cross commutation makes the total fixed intersection the join of the two
individual fixed intersections, hence U∩C(Uˣ)=U∩Uˣ. Using this literal
intersection in the actual full-R supplements gives C_R(Uˣ)=Uˣ C_R(K),
with the same original K-centralizer as C_R(U).

Source: Aschbacher–Smith, C.5.6(7), printed p.160.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G]

private theorem fixed_join_le (A B X Y : Subgroup G)
    (hBA : B ≤ centralizer (A : Set G)) (hBX : B ≤ centralizer (X : Set G))
    (hAY : A ≤ centralizer (Y : Set G))
    (hAX : A ⊓ centralizer (X : Set G) ≤ X)
    (hBY : B ⊓ centralizer (Y : Set G) ≤ Y) :
    (A ⊔ B) ⊓ centralizer (X ⊔ Y : Subgroup G) ≤ X ⊔ Y := by
  rintro u ⟨hu,hc⟩
  have hm : u ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hBA.trans (Subgroup.centralizer_le_normalizer _))]
    exact hu
  obtain ⟨a,ha,b,hb,rfl⟩ := hm
  have haX : a ∈ centralizer (X : Set G) := by
    intro x hx
    have hh : (x*a)*b=(a*x)*b := by
      calc
        _ = x*(a*b) := mul_assoc _ _ _
        _ = (a*b)*x := hc x (mem_sup_left hx)
        _ = (a*x)*b := by rw [mul_assoc,← hBX hb x hx,← mul_assoc]
    exact mul_right_cancel hh
  have hbY : b ∈ centralizer (Y : Set G) := by
    intro y hy
    have hh : a*(y*b)=a*(b*y) := by
      calc
        _ = y*(a*b) := by rw [← mul_assoc,← hAY ha y hy,mul_assoc]
        _ = (a*b)*y := hc y (mem_sup_right hy)
        _ = a*(b*y) := mul_assoc _ _ _
    exact mul_left_cancel hh
  exact mul_mem_sup (hAX ⟨ha,haX⟩) (hBY ⟨hb,hbY⟩)

variable [Finite G] {R K L : Subgroup G} {F F' : Type*} [Field F] [Field F']

theorem Setup.two_block_fixed_intersection
    (h : Setup R K F) (h' : Setup R L F') (hKL : L ≤ centralizer (K : Set G))
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M) (hxR : x ∈ normalizer (R : Set G))
    (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let U₀ := U K ⊔ U L
    let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
    U₀ ⊓ centralizer (V : Set G) = U₀ ⊓ V := by
  let U₀ := U K ⊔ U L
  let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hh := FourModuleOrbit.cross_commutators hi.toInputs
  have hf1 : U K ⊓ centralizer ((U K).conjBy x⁻¹ : Set G) ≤ (U K).conjBy x⁻¹ := by
    change U K ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ _
    rw [← (h.commutator_eq_fixed hxR hnc).1,(h.commutator_eq_fixed hxR hnc).2]
    exact inf_le_right
  have hf2 : U L ⊓ centralizer ((U L).conjBy x⁻¹ : Set G) ≤ (U L).conjBy x⁻¹ := by
    change U L ⊓ centralizer ((U L).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ _
    rw [← (h'.commutator_eq_fixed hxR (second_noncommuting hi)).1,
      (h'.commutator_eq_fixed hxR (second_noncommuting hi)).2]
    exact inf_le_right
  have hBA := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh.1)
  have hfixed := fixed_join_le (U K) (U L) ((U K).conjBy x⁻¹) ((U L).conjBy x⁻¹) hBA
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh.2.2.1))
    (commutator_eq_bot_iff_le_centralizer.mp hh.2.1) hf1 hf2
  let := h.elementary
  let := h'.elementary
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.sup_of_le_centralizer hBA
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  change U₀ ⊓ centralizer (V : Set G) = U₀ ⊓ V
  apply le_antisymm
  · apply le_inf inf_le_left
    change (U K ⊔ U L) ⊓ centralizer (V : Set G) ≤ V
    rw [show V = (U K).conjBy x⁻¹ ⊔ (U L).conjBy x⁻¹ from Subgroup.map_sup _ _ _]
    exact hfixed
  · exact le_inf inf_le_left (inf_le_right.trans (le_centralizer V))

theorem Setup.two_block_conjugate_full_centralizer_product
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hSylow' : (∃ n, IsL2EvenBlock L n) →
      ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S R ⊓ L)
    (M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (x : G) (hx : x ∈ M) (hxR : x ∈ normalizer (R : Set G))
    (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let U₀ := U K ⊔ U L
    let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
    R ⊓ centralizer (V : Set G) = V ⊔ (R ⊓ centralizer (K ⊔ L : Subgroup G)) := by
  let U₀ := U K ⊔ U L
  let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
  let P := R ⊓ centralizer (U₀ : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  let C := R ⊓ centralizer (K ⊔ L : Subgroup G)
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hprod := h.two_block_full_centralizer_product h' hR hKL hSylow hSylow' M T_H hRTH hTHM
    x hx hxR hindex hpair ht hnc
  have hCV := h.two_block_full_centralizer_centralizes h' hR hKL hSylow hSylow' M T_H hRTH hTHM
    x hx hxR hindex hpair ht hnc
  have hmut := h.two_block_mutual_centralizers h' hR hKL hSylow hSylow' M T_H hRTH hTHM
    x hx hxR hindex hpair ht hnc
  have hfix := h.two_block_fixed_intersection h' hKL M T_H x hx hxR hindex hpair ht hnc
  have hCU : C ≤ centralizer (U₀ : Set G) := inf_le_right.trans
    (centralizer_le (sup_le_sup (map_subtype_le _) (map_subtype_le _)))
  have hPN : P ≤ normalizer (V : Set G) := by
    intro r hr
    have hh : r ∈ M ⊓ normalizer (FourModuleOrbit.modules (U K) (U L) x 0 : Set G) :=
      ⟨hTHM (hRTH hr.1),Subgroup.centralizer_le_normalizer _
        (centralizer_le (show U K ≤ U₀ from le_sup_left) hr.2)⟩
    have hn1 : r ∈ normalizer ((U K).conjBy x⁻¹ : Set G) := ((hi.normalizers_eq 0 2) ▸ hh).2
    have hn2 : r ∈ normalizer ((U L).conjBy x⁻¹ : Set G) := ((hi.normalizers_eq 0 3) ▸ hh).2
    have he1 : ((U K).conjBy x⁻¹).map (MulAut.conj r).toMonoidHom = (U K).conjBy x⁻¹ :=
      mem_normalizer_iff_map_conj_eq.mp hn1
    have he2 : ((U L).conjBy x⁻¹).map (MulAut.conj r).toMonoidHom = (U L).conjBy x⁻¹ :=
      mem_normalizer_iff_map_conj_eq.mp hn2
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (U₀.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj r).toMonoidHom = _
    rw [show U₀.map (MulAut.conj x⁻¹).toMonoidHom = (U K).conjBy x⁻¹ ⊔ (U L).conjBy x⁻¹ from Subgroup.map_sup _ _ _,
      Subgroup.map_sup,he1,he2]
    exact (Subgroup.map_sup _ _ _).symm
  let := h.elementary
  let := h'.elementary
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.sup_of_le_centralizer
    ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _))))
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hVR : V ≤ R := (map_mono (sup_le h.module_le h'.module_le)).trans
    ((h.stable hxR).le.trans inf_le_left)
  change P' = V ⊔ C
  apply le_antisymm
  · intro a ha
    have hm : a ∈ (V : Set G) * (P : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left V P hPN]
      exact hmut.1 ha
    obtain ⟨v,hv,p,hp,hvp⟩ := hm
    have hpV : p ∈ centralizer (V : Set G) := by
      have hh := (centralizer (V : Set G)).mul_mem
        ((centralizer (V : Set G)).inv_mem (le_centralizer V hv)) ha.2
      rw [← hvp] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hp' : p ∈ (U₀ : Set G) * (C : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U₀ C (hCU.trans (Subgroup.centralizer_le_normalizer _))]
      exact hprod ▸ hp
    obtain ⟨u,hu,c,hc,huc⟩ := hp'
    have huV : u ∈ centralizer (V : Set G) := by
      have hh := (centralizer (V : Set G)).mul_mem hpV ((centralizer (V : Set G)).inv_mem (hCV hc))
      rw [← huc] at hh
      simpa only [mul_inv_cancel_right] using hh
    have hu' : u ∈ V := (hfix ▸ (show u ∈ U₀ ⊓ centralizer (V : Set G) from ⟨hu,huV⟩)).2
    rw [← hvp,← huc]
    change v*(u*c) ∈ V ⊔ C
    rw [← mul_assoc]
    exact mul_mem_sup (V.mul_mem hv hu') hc
  · exact sup_le (le_inf hVR (le_centralizer V)) (le_inf inf_le_left hCV)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
