module
public import Theory.GroupAction.PrimitivePrimeSylowAction
public import Theory.GroupTheory.TINormalizerControl
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Automizers of central elementary subgroups of order eight

If an elementary subgroup Z of order eight is central in a Sylow
2-subgroup, its full automizer has odd order dividing 21. A subgroup C
of order prime to three therefore acts on Z through a group of order
at most seven. A faithful Cartan subgroup of order seven exhausts this
action, giving the exact normalizer-centralizer factorization in C.

When Z has trivial intersections under C and the Cartan acts freely on
nonidentity elements, C_C(z) = C_C(Z) for every nonidentity z in Z.
Intersecting conjugates under N_G(C) consequently have the same
pointwise C-centralizer, and their transporter normalizes that subgroup.
This conclusion does not assert that the conjugate points coincide.

The actual consumer is the degree-three branch of Aschbacher–Smith
5.1.17, printed p.640 (refs/quasithin.pdf), in OddSetupPointCentralizers.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A central eight-group has an odd automizer of order dividing 21. -/
theorem central_eight_automizer_card_dvd
    (T : Sylow 2 G) (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZ : Nat.card Z = 8) (hc : (T : Subgroup G) ≤ centralizer (Z : Set G)) :
    Nat.card Z.normalizerMonoidHom.range ∣ 21 := by
  have hn := hc.trans (centralizer_le_normalizer (Z : Set G))
  let S := T.subtype hn
  have hs : (S : Subgroup (normalizer (Z : Set G))) ≤ Z.normalizerMonoidHom.ker := by
    intro t ht
    rw [normalizerMonoidHom_ker]
    exact hc ht
  have hodd : ¬ 2 ∣ Nat.card Z.normalizerMonoidHom.range := by
    rw [← index_ker]
    exact fun hh => S.not_dvd_index (hh.trans (index_dvd_of_le hs))
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := 3) Z (by omega)
  have hd := (card_subgroup_dvd_card Z.normalizerMonoidHom.range).trans
    (card_dvd_of_injective f hf)
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ, ZMod.card]
  rw [hgl] at hd
  have hcop : Nat.Coprime (Nat.card Z.normalizerMonoidHom.range) 8 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm.pow_right 3
  exact hcop.dvd_of_dvd_mul_left (show Nat.card Z.normalizerMonoidHom.range ∣ 8*21 from hd)

/-- Removing three from the actor leaves an automizer of order dividing seven. -/
theorem central_eight_three_free_action_card_dvd
    (T : Sylow 2 G) (Z C : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZ : Nat.card Z = 8) (hc : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (h3 : ¬ 3 ∣ Nat.card C) :
    Nat.card (Z.normalizerMonoidHom.comp
      (inclusion (show C ⊓ normalizer (Z : Set G) ≤ normalizer (Z : Set G) from inf_le_right))).range ∣ 7 := by
  let f := Z.normalizerMonoidHom.comp
      (inclusion (show C ⊓ normalizer (Z : Set G) ≤ normalizer (Z : Set G) from inf_le_right))
  have hle : f.range ≤ Z.normalizerMonoidHom.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion inf_le_right x,rfl⟩
  have hd : Nat.card f.range ∣ 21 := (card_dvd_of_le hle).trans
    (central_eight_automizer_card_dvd T Z hZ hc)
  have hfree : ¬ 3 ∣ Nat.card f.range := fun hh => h3
    (hh.trans ((card_range_dvd f).trans (card_dvd_of_le (show C ⊓ normalizer (Z : Set G) ≤ C from inf_le_left))))
  exact (Nat.prime_three.coprime_iff_not_dvd.mpr hfree).symm.dvd_of_dvd_mul_left hd

/-- The faithful seven-group supplies the entire action of the point stabilizer. -/
theorem central_eight_three_free_stabilizer_factor
    (T : Sylow 2 G) (Z C A : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZ : Nat.card Z = 8) (hc : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (h3 : ¬ 3 ∣ Nat.card C) (hAC : A ≤ C)
    (hAZ : A ≤ normalizer (Z : Set G)) (hA : Nat.card A = 7)
    (hfaith : Disjoint A (centralizer (Z : Set G))) :
    C ⊓ normalizer (Z : Set G) = A ⊔ (C ⊓ centralizer (Z : Set G)) := by
  let J := C ⊓ normalizer (Z : Set G)
  let f := Z.normalizerMonoidHom.comp (inclusion (show J ≤ normalizer (Z : Set G) from inf_le_right))
  let a := Z.normalizerMonoidHom.comp (inclusion hAZ)
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hh : inclusion hAZ x ∈ Z.normalizerMonoidHom.ker := hx
    rw [normalizerMonoidHom_ker] at hh
    exact Subtype.ext (hfaith.le_bot ⟨x.property,hh⟩)
  have hcard : Nat.card a.range = 7 :=
    (Nat.card_congr (MonoidHom.ofInjective ha).toEquiv).symm.trans hA
  have hle : a.range ≤ f.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨x,⟨hAC x.property,hAZ x.property⟩⟩,rfl⟩
  have he : a.range = f.range := eq_of_le_of_card_ge hle (by
    rw [hcard]
    exact Nat.le_of_dvd (by decide) (central_eight_three_free_action_card_dvd T Z C hZ hc h3))
  apply le_antisymm _ (sup_le (le_inf hAC hAZ)
    (le_inf inf_le_left (inf_le_right.trans (centralizer_le_normalizer _))))
  intro x hx
  have hm : f ⟨x,hx⟩ ∈ a.range := he.symm ▸ (show f ⟨x,hx⟩ ∈ f.range from ⟨_,rfl⟩)
  obtain ⟨b,hb⟩ := hm
  have hk : (inclusion hAZ b)⁻¹ * inclusion (show J ≤ normalizer (Z : Set G) from inf_le_right) ⟨x,hx⟩ ∈
      Z.normalizerMonoidHom.ker := by
    change Z.normalizerMonoidHom (_⁻¹ * _) = 1
    rw [map_mul,map_inv]
    change (a b)⁻¹ * f ⟨x,hx⟩ = 1
    rw [hb,inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hh := (A ⊔ (C ⊓ centralizer (Z : Set G))).mul_mem
    (mem_sup_left b.property)
    (mem_sup_right (show (b : G)⁻¹*x ∈ C ⊓ centralizer (Z : Set G) from
      ⟨C.mul_mem (C.inv_mem (hAC b.property)) hx.1,hk⟩))
  simpa only [mul_inv_cancel_left] using hh

open scoped Pointwise in
/-- Local TI and the free Cartan action identify all nonidentity point centralizers. -/
theorem central_eight_elementCentralizer_eq
    (T : Sylow 2 G) (Z C A : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZ : Nat.card Z = 8) (hc : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (h3 : ¬ 3 ∣ Nat.card C) (hAC : A ≤ C)
    (hAZ : A ≤ normalizer (Z : Set G)) (hA : Nat.card A = 7)
    (hfaith : Disjoint A (centralizer (Z : Set G)))
    (hfree : ∀ a ∈ A, ∀ z ∈ Z, z ≠ 1 → a*z = z*a → a = 1)
    (hti : ∀ g ∈ C, Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hz)))
  intro x hx
  have hxN := inf_elementCentralizer_le_normalizer_of_trivial_intersections hti hz hz1 hx
  have hfactor := central_eight_three_free_stabilizer_factor T Z C A hZ hc h3 hAC hAZ hA hfaith
  let K := C ⊓ centralizer (Z : Set G)
  have hn : A ≤ normalizer (K : Set G) :=
    (le_inf (hAC.trans C.le_normalizer)
      (hAZ.trans (normalizer_le_normalizer_centralizer Z))).trans inf_normalizer_le_normalizer_inf
  have hm : x ∈ (K : Set G) * (A : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K A hn, sup_comm K A]
    exact hfactor ▸ (show x ∈ C ⊓ normalizer (Z : Set G) from ⟨hx.1,hxN⟩)
  obtain ⟨k,hk,a,ha,rfl⟩ := hm
  have hax : a*z = z*a := by
    have hxz := mem_centralizer_singleton_iff.mp hx.2
    have hkz := mem_centralizer_iff.mp hk.2 z hz
    apply mul_left_cancel (a := k)
    calc
      k*(a*z) = z*(k*a) := by simpa only [mul_assoc] using hxz
      _ = k*(z*a) := by rw [←mul_assoc,hkz,mul_assoc]
  change k*a ∈ C ⊓ centralizer (Z : Set G)
  rw [hfree a ha z hz hz1 hax,mul_one]
  exact hk

omit [Finite G] in
private theorem centralizer_conjugate_eq_of_point_centralizers
    (Z C : Subgroup G)
    (he : ∀ z ∈ Z, z ≠ 1 → C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z : Set G))
    (e : G ≃* G) (hC : C.map e.toMonoidHom = C) :
    ∀ z ∈ Z.map e.toMonoidHom, z ≠ 1 →
      C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z.map e.toMonoidHom : Set G) := by
  rintro _ ⟨z,hz,rfl⟩ hz1
  have hz1' : z ≠ 1 := by intro hh; exact hz1 (by rw [hh,map_one])
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
    (mem_map_of_mem e.toMonoidHom hz))))
  intro c hc
  have hbC : e.symm c ∈ C := by
    have hm : c ∈ C.map e.toMonoidHom := hC.symm ▸ hc.1
    obtain ⟨b,hb,rfl⟩ := hm
    change e.symm (e b) ∈ C
    simpa only [MulEquiv.symm_apply_apply] using (show b ∈ C from hb)
  have hbz : e.symm c ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using
      (show c * e z = e z * c from mem_centralizer_singleton_iff.mp hc.2)
  have hb := (he z hz hz1').le ⟨hbC,hbz⟩
  refine ⟨hc.1,?_⟩
  rintro _ ⟨v,hv,rfl⟩
  have hh := congrArg e (hb.2 v hv)
  change e v * c = c * e v
  simpa only [map_mul,MulEquiv.apply_symm_apply] using hh

omit [Finite G] in
/-- Intersecting conjugate points have the same pointwise centralizer in C. -/
theorem centralizers_eq_of_intersecting_conjugates
    (Z C : Subgroup G)
    (he : ∀ z ∈ Z, z ≠ 1 → C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z : Set G))
    {g : G} (hg : g ∈ normalizer (C : Set G))
    (hx : Z ⊓ Z.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    C ⊓ centralizer (Z : Set G) =
      C ⊓ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨x,hxZ,hx1⟩ := SetLike.not_le_iff_exists.mp (mt le_bot_iff.mp hx)
  have hx1' : x ≠ 1 := by simpa only [mem_bot] using hx1
  exact (he x hxZ.1 hx1').symm.trans
    (centralizer_conjugate_eq_of_point_centralizers Z C he (MulAut.conj g)
      (mem_normalizer_iff_map_conj_eq.mp hg) x hxZ.2 hx1')

/-- An intersecting conjugator preserves the common pointwise centralizer. -/
theorem centralizer_normalizer_of_intersecting_conjugates
    (Z C : Subgroup G)
    (he : ∀ z ∈ Z, z ≠ 1 → C ⊓ centralizer ({z} : Set G) = C ⊓ centralizer (Z : Set G))
    {g : G} (hg : g ∈ normalizer (C : Set G))
    (hx : Z ⊓ Z.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    g ∈ normalizer ((C ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := by
  have hC := mem_normalizer_iff_map_conj_eq.mp hg
  have hsame := centralizers_eq_of_intersecting_conjugates Z C he hg hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · apply le_trans _ hsame.ge
    exact le_inf ((map_mono inf_le_left).trans hC.le)
      ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ _))
  · rw [card_map_of_injective (MulAut.conj g).injective]
end Subgroup
