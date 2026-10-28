module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SeedFusion
public import Theory.SpecificGroups.PSL3Two.Parabolics.OddIndex
public import Theory.GroupTheory.PCoreImage

/-!
# The quaternion core in the aligned local intersection

The intersection of H with a Sylow-aligned conjugate of M has order 192.
Its image in M/V is an actual index-seven parabolic, with two-core of
order four. Lifting that core gives order 32. The normal quaternion
subgroup Q₁Q₂ already lies in the intersection, hence it is exactly this
two-core. Consequently the entire conjugate elementary eight lies in Q₁Q₂.
It is normalized and self-centralizing in the original H-Sylow.

All conjugations and subgroup inclusions are retained. This strengthens
the seed alignment used in the extension step of Aschbacher–Smith I.4.5,
printed p.417, and Fong–Wong §2F, Nagoya Math. J.36 (1969), pp.153–154.
It is not the ambient recognition theorem, which remains with
`qt-i45-g2-recognition`. The Chapter14 application is in Chapter14Extension.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.V_normal V_elementary

theorem M_parabolic_core (A : Subgroup c.M) (hVA : c.V ≤ A)
    (hA : Nat.card A = 192) :
    c.V ≤ A.pCoreIn 2 ∧ Nat.card (A.pCoreIn 2) = 32 := by
  let e := c.quotient_model.some.trans Matrix.PSL3Two.equiv.symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' c.V)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective c.V)
  have hk : q.ker = c.V := by
    ext x
    change e (QuotientGroup.mk' c.V x) = 1 ↔ x ∈ c.V
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 q.ker := hk ▸ IsElementaryAbelian.isPGroup 2 c.V
  have hAi : A.index = 7 := by
    have hh := A.card_mul_index
    rw [hA, M_card c] at hh
    omega
  let B := A.map q
  have hBi : B.index = 7 := (A.index_map_eq hq (hk ▸ hVA)).trans hAi
  have hBc : Nat.card B = 24 := by
    have hh := B.card_mul_index
    rw [hBi, Matrix.PSL3Two.card_SL] at hh
    omega
  have hBne : B ≠ ⊤ := by intro h; simp only [h, index_top] at hBi; omega
  have hBtwo : ¬ IsPGroup 2 B := by
    intro h
    obtain ⟨n, hn⟩ := h.exists_card_eq
    have hd : 3 ∣ 2 ^ n := hn ▸ (hBc ▸ (by decide : 3 ∣ 24))
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hc := (Matrix.PSL3Two.odd_index_core_data B hBne (hBi ▸ (by decide)) hBtwo).2
  have hVK : c.V ≤ A.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 c.V) hVA (by rw [c.V.normalizer_eq_top]; exact le_top)
  have hmap : (A.pCoreIn 2).map q = B.pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup q hp A
  have hh := (c.V.subgroupOf (A.pCoreIn 2)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv, V_card c] at hh
  change 8 * c.V.relIndex (A.pCoreIn 2) = Nat.card (A.pCoreIn 2) at hh
  rw [← hk, relIndex_ker, hmap, hc] at hh
  exact ⟨hVK, hh.symm⟩

theorem aligned_core (g : G)
    (hV : (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom ≤ c.H)
    (hQ : (quaternionCore c).map c.H.subtype ≤ c.M.map (MulAut.conj g).toMonoidHom)
    (hI : Nat.card (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom : Subgroup G) = 192) :
    (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).pCoreIn 2 =
      (quaternionCore c).map c.H.subtype ∧
    (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom ≤
      (quaternionCore c).map c.H.subtype := by
  let f : c.M →* G := (MulAut.conj g).toMonoidHom.comp c.M.subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp c.M.subtype_injective
  have hfr : f.range = c.M.map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp, c.M.range_subtype]
  let A := c.H.comap f
  let Q := (quaternionCore c).map c.H.subtype
  let I := c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom
  have hAI : A.map f = I := by rw [map_comap_eq, hfr]; exact inf_comm _ _
  have hVA : c.V ≤ A := by
    intro v hv
    exact hV (by rw [map_map]; exact mem_map_of_mem f hv)
  have hAc : Nat.card A = 192 := by
    rw [← card_map_of_injective hf, hAI]
    exact hI
  obtain ⟨hVK, hK⟩ := M_parabolic_core c A hVA hAc
  have hmap : (A.pCoreIn 2).map f = I.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup f (by
      rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]
      exact IsPGroup.of_card (n := 0) (by simp)), hAI]
  have hcorecard : Nat.card (I.pCoreIn 2) = 32 := by
    rw [← hmap, card_map_of_injective hf, hK]
  have hQI : Q ≤ I := le_inf (map_subtype_le _) hQ
  have hnorm : I ≤ normalizer (Q : Set G) := by
    apply inf_le_left.trans
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    change ((quaternionCore c).map c.H.subtype |>.comap c.H.subtype).Normal
    rw [comap_map_eq_self_of_injective c.H.subtype_injective]
    infer_instance
  have hQcore : Q ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsPGroup.of_card (p := 2) (n := 5) (quaternionCore_card c)).map c.H.subtype)
    hQI hnorm
  have heq : Q = I.pCoreIn 2 := eq_of_le_of_card_ge hQcore (by
    rw [hcorecard, card_map_of_injective c.H.subtype_injective, quaternionCore_card c])
  refine ⟨heq.symm, ?_⟩
  rw [map_map]
  change c.V.map f ≤ Q
  rw [heq, ← hmap]
  exact map_mono hVK

theorem exists_seed_in_quaternionCore (T : Sylow 2 c.H) :
    ∃ (E : Subgroup c.H) (g : G), IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      E ≤ quaternionCore c ∧ (T : Subgroup c.H) ≤ normalizer (E : Set c.H) ∧
      (T : Subgroup c.H) ⊓ centralizer (E : Set c.H) = E ∧
      E.map c.H.subtype = (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom ∧
      (T : Subgroup c.H).map c.H.subtype ≤ c.M.map (MulAut.conj g).toMonoidHom ∧
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).pCoreIn 2 =
        (quaternionCore c).map c.H.subtype := by
  obtain ⟨z,hz,hgen,hH⟩ := exists_marked_involution c
  have hzQ : z ∈ quaternionCore c := by
    have hh : z ∈ c.H₁ ⊓ c.H₂ := hgen ▸ mem_zpowers z
    rw [← quaternionCore_center c] at hh
    exact map_subtype_le _ hh
  obtain ⟨E,he,hc,hET,_,⟨g,hE,hTM,hI⟩,_⟩ := exists_seed_in_H_sylow c T z hz
    (quaternionCore_le_sylow c T hzQ) hH
  let a := MulAut.conj g
  let f : c.M →* G := a.toMonoidHom.comp c.M.subtype
  have hf : Function.Injective f := a.injective.comp c.M.subtype_injective
  have hEf : E.map c.H.subtype = c.V.map f := by rw [hE,map_map]
  have hM : f.range = c.M.map a.toMonoidHom := by rw [MonoidHom.range_comp,c.M.range_subtype]
  have hVT : c.V.map f ≤ (T : Subgroup c.H).map c.H.subtype := hEf ▸ map_mono hET
  obtain ⟨hcore,hVQ⟩ := aligned_core c g (hE ▸ map_subtype_le E)
    ((map_mono (quaternionCore_le_sylow c T)).trans hTM) hI
  have hEQ : E ≤ quaternionCore c := by
    apply (map_le_map_iff_of_injective c.H.subtype_injective).mp
    rwa [hE]
  have hnorm : (T : Subgroup c.H) ≤ normalizer (E : Set c.H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro x
    have htf : (t : G) ∈ f.range := hM.symm ▸ hTM (mem_map_of_mem c.H.subtype ht)
    obtain ⟨m,hm⟩ := htf
    have hex (y : c.H) : y ∈ E ↔ (y : G) ∈ c.V.map f := by
      rw [← hEf]
      exact (mem_map_iff_mem c.H.subtype_injective).symm
    rw [hex,hex]
    constructor
    · rintro ⟨v,hv,hvx⟩
      refine ⟨m*v*m⁻¹,(inferInstance : c.V.Normal).conj_mem v hv m,?_⟩
      simp only [map_mul,map_inv,hm,hvx]
      rfl
    · rintro ⟨v,hv,hvx⟩
      refine ⟨m⁻¹*v*m,?_,?_⟩
      · have hh := (inferInstance : c.V.Normal).conj_mem v hv m⁻¹
        rw [inv_inv] at hh
        exact hh
      · simp only [map_mul,map_inv,hm]
        change f v = (t : G) * (x : G) * (t : G)⁻¹ at hvx
        rw [hvx]
        group
  have hcent : (T : Subgroup c.H) ⊓ centralizer (E : Set c.H) = E := by
    apply le_antisymm ?_ (le_inf hET (by let _ := he; exact E.le_centralizer))
    intro t ht
    have htf : (t : G) ∈ f.range := hM.symm ▸ hTM (mem_map_of_mem c.H.subtype ht.1)
    obtain ⟨m,hm⟩ := htf
    have hmV : m ∈ c.V := by
      rw [← V_centralizer c]
      intro v hv
      apply hf
      simp only [map_mul,hm]
      obtain ⟨w,hw,hwv⟩ := (hEf.symm ▸ mem_map_of_mem f hv)
      have hh := congrArg Subtype.val (ht.2 w hw)
      change (w : G) * (t : G) = (t : G) * (w : G) at hh
      change (w : G) = f v at hwv
      rwa [hwv] at hh
    have htE : (t : G) ∈ E.map c.H.subtype := hEf.symm ▸ ⟨m,hmV,hm⟩
    exact (mem_map_iff_mem c.H.subtype_injective).mp htE
  exact ⟨E,g,he,hc,hEQ,hnorm,hcent,hE,hTM,hcore⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
