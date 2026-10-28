module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPair
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairSupplement

/-!
# The original A₅ pair has exactly the quaternion two-core

An original involution outside O₂(H) inverts an odd-prime rotation. The
literal starred pair is S₃, forcing that rotation to have order three.
It gives a dihedral supplement of order six to U_H, so the pair has order
at most 192. The original quotient kernel contains U_H and has index six;
therefore O₂(I)=U_H. This is the pair-core step of 13.5.15 used in 13.5.17.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.15, printed p.920 (PDF p.937).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.Section09.Setup.Hypothesis
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

omit hn in
/-- The odd rotation lies in its literal pair and its original starred
image forces its order to be three. -/
theorem normal_odd_rotation_cubic (v r : G) (hv : v ∈ V) (hv2 : v^2=1)
    {p : ℕ} (hp : p.Prime) (hp2 : p≠2) (hr : orderOf r=p)
    (hrH : r∈H) (hi : v*r*v⁻¹=r⁻¹) : p=3 ∧
    ¬IsPGroup 2 (Source.starImage H (V⊔V.map (MulAut.conj r).toMonoidHom)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let I := V⊔V.map (MulAut.conj r).toMonoidHom
  have hrI := NormalBranch.SourceOddRotation.rotation_mem_pair (D:=D) v r hv hv2 hp hp2 hr hi
  let π := QuotientGroup.mk' (pCore 2 H)
  let rH : H := ⟨r,hrH⟩
  have hcop : Nat.Coprime 2 p := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)) |>.symm
  have hk : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk'];exact pCore_isPGroup
  have hpr : orderOf (π rH)=p :=
    (π.orderOf_map_eq_of_coprime_of_isPGroup_ker hk rH (by
      rw [←orderOf_coe rH];exact hr ▸ hcop)).trans ((orderOf_coe rH).symm.trans hr)
  have hm : π rH∈Source.starImage H I := mem_map_of_mem π hrI
  have hnot : ¬IsPGroup 2 (Source.starImage H I) := by
    intro hh
    obtain ⟨n,hn⟩ := hh.exists_pow_pow_eq_one ⟨π rH,hm⟩
    have hd : p∣2^n := hpr ▸ orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  obtain ⟨j⟩ := hf.pair_star_symmetricThree d.third_index d.module_card
    (fun _ hk hi => source13_5_13_one d hA312 hH hU hk hi)
    (source_seed_centralizer_bound d hA312) r hrH hnot
  have hc : Nat.card (Source.starImage H I)=6 := by
    change Source.starImage H I ≃* Equiv.Perm (Fin 3) at j
    rw [Nat.card_congr j.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hd : p∣6 := hc ▸ hpr ▸ (Source.starImage H I).orderOf_dvd_natCard hm
  have h3 : p=3 := by
    have hh : p∣2 ∨ p∣3 := hp.dvd_mul.mp (show p∣2*3 from hd)
    rcases hh with hh|hh
    · exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh)).elim
    · exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh
  exact ⟨h3,hnot⟩

/-- The actual order-six supplement bounds the original pair order. -/
theorem normal_pair_card_le (v r : G) (hv : v∈V) (hvq : v∉Source.QH H)
    (hv2 : v^2=1) (hr : orderOf r=3) (hrH : r∈H) (hi : v*r*v⁻¹=r⁻¹) :
    Nat.card (V⊔V.map (MulAut.conj r).toMonoidHom : Subgroup G)≤192 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let I := V⊔V.map (MulAut.conj r).toMonoidHom
  let J := D.UH⊔(zpowers r⊔zpowers v)
  have hp := (normal_odd_rotation_cubic d hA312 hH hU v r hv hv2
    (by decide:Nat.Prime 3) (by decide:3≠2) hr hrH hi).2
  have he : V₃⊔V₃.map (MulAut.conj r).toMonoidHom=D.UH := by
    change V₃⊔V₃.map (MulAut.conj r).toMonoidHom=Source.UH H V₃
    simpa only [ChapterG.Section02.Setup.conjugate,inv_inv] using
      normal_pair_seed_eq d hA312 hH hU hn (g:=r⁻¹) (H.inv_mem hrH)
        (by unfold ChapterG.Section02.Setup.conjugate; rw [inv_inv]; exact hp)
  have hUI : D.UH≤I := he ▸ sup_le_sup d.third_le (map_mono d.third_le)
  have hrI := NormalBranch.SourceOddRotation.rotation_mem_pair (D:=D) v r hv hv2
    (by decide:Nat.Prime 3) (by decide:3≠2) hr hi
  have hIJ : I=J := by
    apply le_antisymm
    · have hvplus : v∉V₃ := fun hh=>hvq (hf.UH_le_QH (le_conjugateSpanBy _ _ hh))
      have hV : V≤J := by
        rw [←sup_zpowers_eq_of_relIndex_prime d.third_le Nat.prime_two d.third_index hv hvplus]
        exact sup_le ((le_conjugateSpanBy _ _).trans le_sup_left)
          (le_sup_right.trans le_sup_right)
      refine sup_le hV ?_
      rintro _ ⟨x,hx,rfl⟩
      have hrJ : r∈J := mem_sup_right (mem_sup_left (mem_zpowers r))
      exact J.mul_mem (J.mul_mem hrJ (hV hx)) (J.inv_mem hrJ)
    · exact sup_le hUI (sup_le (zpowers_le.mpr hrI) (zpowers_le.mpr (mem_sup_left hv)))
  change Nat.card I≤192
  rw [hIJ]
  have hjH : zpowers r⊔zpowers v≤H :=
    sup_le (zpowers_le.mpr hrH) (zpowers_le.mpr (hf.V_le_H hv))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.UH (zpowers r⊔zpowers v)
    (hjH.trans (le_normalizer_conjugateSpanBy V₃ H))
  obtain ⟨q,_⟩ := normal_quaternion_with_center d hA312 hH hU hn
  change QuaternionCentralProductData D.UH at q
  rw [q.card,NormalBranch.SourcePairSupplement.supplement_card (D:=D) v r hvq hv2 hr hi] at hc
  have hpos := Nat.card_pos (α:=(D.UH⊓(zpowers r⊔zpowers v):Subgroup G))
  change Nat.card (D.UH⊔(zpowers r⊔zpowers v):Subgroup G)≤192
  nlinarith

/-- The pair two-core is precisely the already constructed U_H. -/
theorem normal_pair_core_eq (v r : G) (hv : v∈V) (hvq : v∉Source.QH H)
    (hv2 : v^2=1) (hr : orderOf r=3) (hrH : r∈H) (hi : v*r*v⁻¹=r⁻¹) :
    (V⊔V.map (MulAut.conj r).toMonoidHom).pCoreIn 2=Source.UH H V₃ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let I := V⊔V.map (MulAut.conj r).toMonoidHom
  have hIH : I≤H := sup_le hf.V_le_H (by
    rintro _ ⟨x,hx,rfl⟩
    exact H.mul_mem (H.mul_mem hrH (hf.V_le_H hx)) (H.inv_mem hrH))
  have hp := (normal_odd_rotation_cubic d hA312 hH hU v r hv hv2
    (by decide:Nat.Prime 3) (by decide:3≠2) hr hrH hi).2
  have he : V₃⊔V₃.map (MulAut.conj r).toMonoidHom=D.UH := by
    change V₃⊔V₃.map (MulAut.conj r).toMonoidHom=Source.UH H V₃
    simpa only [ChapterG.Section02.Setup.conjugate,inv_inv] using
      normal_pair_seed_eq d hA312 hH hU hn (g:=r⁻¹) (H.inv_mem hrH)
        (by unfold ChapterG.Section02.Setup.conjugate; rw [inv_inv]; exact hp)
  have hUI : D.UH≤I := he ▸ sup_le_sup d.third_le (map_mono d.third_le)
  obtain ⟨j⟩ := hf.pair_star_symmetricThree d.third_index d.module_card
    (fun _ hk hi => source13_5_13_one d hA312 hH hU hk hi)
    (source_seed_centralizer_bound d hA312) r hrH hp
  let f := pairProjection (D:=D) I hIH
  let j' := (MulEquiv.subgroupCongr (pairProjection_range (D:=D) I hIH)).trans j
  let η := j'.toMonoidHom.comp f.rangeRestrict
  have hη : Function.Surjective η := j'.surjective.comp f.rangeRestrict_surjective
  have hk : η.ker=f.ker := by
    ext x
    change j' (f.rangeRestrict x)=1↔f x=1
    rw [j'.map_eq_one_iff]
    exact Subtype.ext_iff
  have htwo : IsPGroup 2 η.ker := by
    rw [hk,pairProjection_ker]
    exact (isPGroup_pCoreIn 2 H).comap_subtype
  have hcore : f.ker=pCore 2 I := hk.symm.trans (ker_eq_twoCore_of_surjective_perm_three η hη htwo)
  have hc : Nat.card f.range=6 := by
    rw [Nat.card_congr j'.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hcount := f.ker.index_mul_card
  rw [index_ker,hc] at hcount
  have hbound := normal_pair_card_le d hA312 hH hU hn v r hv hvq hv2 hr hrH hi
  have hkerCard : Nat.card f.ker≤32 := by change Nat.card I≤192 at hbound;omega
  have hUker : D.UH.subgroupOf I≤f.ker := by
    rw [pairProjection_ker]
    exact comap_mono hf.UH_le_QH
  obtain ⟨q,_⟩ := normal_quaternion_with_center d hA312 hH hU hn
  have hUcard : Nat.card (D.UH.subgroupOf I)=32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUI).toEquiv).trans q.card
  have heq : D.UH.subgroupOf I=f.ker := eq_of_le_of_card_ge hUker (by rw [hUcard];exact hkerCard)
  change (pCore 2 I).map I.subtype=D.UH
  rw [←hcore,←heq,map_subgroupOf_eq_of_le hUI]

/-! The same quotient calculation also fixes the literal pair order. -/

theorem normal_pair_card_eq_192 (v r : G) (hv : v∈V) (hvq : v∉Source.QH H)
    (hv2 : v^2=1) (hr : orderOf r=3) (hrH : r∈H) (hi : v*r*v⁻¹=r⁻¹) :
    Nat.card (V⊔V.map (MulAut.conj r).toMonoidHom : Subgroup G)=192 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let I := V⊔V.map (MulAut.conj r).toMonoidHom
  have hIH : I≤H := sup_le hf.V_le_H (by
    rintro _ ⟨x,hx,rfl⟩
    exact H.mul_mem (H.mul_mem hrH (hf.V_le_H hx)) (H.inv_mem hrH))
  have hp := (normal_odd_rotation_cubic d hA312 hH hU v r hv hv2
    (by decide:Nat.Prime 3) (by decide:3≠2) hr hrH hi).2
  have he : V₃⊔V₃.map (MulAut.conj r).toMonoidHom=D.UH := by
    change V₃⊔V₃.map (MulAut.conj r).toMonoidHom=Source.UH H V₃
    simpa only [ChapterG.Section02.Setup.conjugate,inv_inv] using
      normal_pair_seed_eq d hA312 hH hU hn (g:=r⁻¹) (H.inv_mem hrH)
        (by unfold ChapterG.Section02.Setup.conjugate; rw [inv_inv]; exact hp)
  have hUI : D.UH≤I := he ▸ sup_le_sup d.third_le (map_mono d.third_le)
  obtain ⟨j⟩ := hf.pair_star_symmetricThree d.third_index d.module_card
    (fun _ hk hi => source13_5_13_one d hA312 hH hU hk hi)
    (source_seed_centralizer_bound d hA312) r hrH hp
  let f := pairProjection (D:=D) I hIH
  let j' := (MulEquiv.subgroupCongr (pairProjection_range (D:=D) I hIH)).trans j
  let η := j'.toMonoidHom.comp f.rangeRestrict
  have hη : Function.Surjective η := j'.surjective.comp f.rangeRestrict_surjective
  have hk : η.ker=f.ker := by
    ext x
    change j' (f.rangeRestrict x)=1↔f x=1
    rw [j'.map_eq_one_iff]
    exact Subtype.ext_iff
  have htwo : IsPGroup 2 η.ker := by
    rw [hk,pairProjection_ker]
    exact (isPGroup_pCoreIn 2 H).comap_subtype
  have hcore : f.ker=pCore 2 I := hk.symm.trans
    (ker_eq_twoCore_of_surjective_perm_three η hη htwo)
  have hc : Nat.card f.range=6 := by
    rw [Nat.card_congr j'.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hcount := f.ker.index_mul_card
  rw [index_ker,hc] at hcount
  have hbound := normal_pair_card_le d hA312 hH hU hn v r hv hvq hv2 hr hrH hi
  have hkerCard : Nat.card f.ker≤32 := by
    change Nat.card I≤192 at hbound
    omega
  have hUker : D.UH.subgroupOf I≤f.ker := by
    rw [pairProjection_ker]
    exact comap_mono hf.UH_le_QH
  obtain ⟨q,_⟩ := normal_quaternion_with_center d hA312 hH hU hn
  change QuaternionCentralProductData D.UH at q
  have hUcard : Nat.card (D.UH.subgroupOf I)=32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUI).toEquiv).trans q.card
  have heq : D.UH.subgroupOf I=f.ker :=
    eq_of_le_of_card_ge hUker (by rw [hUcard];exact hkerCard)
  rw [←heq,hUcard] at hcount
  change Nat.card I=192
  omega

/-! The exact order and the exact two-core give the order-six quotient used
in the next normal-pair paragraph. -/

theorem normal_pair_index_eq_six (v r : G) (hv : v∈V) (hvq : v∉Source.QH H)
    (hv2 : v^2=1) (hr : orderOf r=3) (hrH : r∈H) (hi : v*r*v⁻¹=r⁻¹) :
    ((Source.UH H V₃).subgroupOf
      (V⊔V.map (MulAut.conj r).toMonoidHom : Subgroup G)).index=6 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  let I := V⊔V.map (MulAut.conj r).toMonoidHom
  have hcore := normal_pair_core_eq d hA312 hH hU hn v r hv hvq hv2 hr hrH hi
  have hUI : D.UH≤I := by
    change Source.UH H V₃ ≤ I
    rw [←hcore]
    exact pCoreIn_le 2 I
  obtain ⟨q,_⟩ := normal_quaternion_with_center d hA312 hH hU hn
  change QuaternionCentralProductData D.UH at q
  have hUcard : Nat.card (D.UH.subgroupOf I)=32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUI).toEquiv).trans q.card
  have hIcard : Nat.card I = 192 :=
    normal_pair_card_eq_192 d hA312 hH hU hn v r hv hvq hv2 hr hrH hi
  have hcount := (D.UH.subgroupOf I).index_mul_card
  rw [hUcard,hIcard] at hcount
  change (D.UH.subgroupOf I).index=6
  omega

/-- Original 13.5.15 supplies its required pair without an additional
choice, two-core, order or quotient-identification premise. -/
theorem source_normal_pair_core : ∃v∈V, v∉Source.QH H ∧ v^2=1 ∧
    ∃r∈H, orderOf r=3 ∧ v*r*v⁻¹=r⁻¹ ∧
      (V⊔V.map (MulAut.conj r).toMonoidHom).pCoreIn 2=Source.UH H V₃ ∧
      Nonempty (Source.starImage H (V⊔V.map (MulAut.conj r).toMonoidHom)≃*
        Equiv.Perm (Fin 3)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨v,hv,hvq,hv2,p,hp,hp2,r,hrH,hr,hi⟩ :=
    NormalBranch.SourceOddRotation.exists_odd_rotation hf hU
  obtain ⟨hp3,hpair⟩ := normal_odd_rotation_cubic d hA312 hH hU v r hv hv2 hp hp2 hr hrH hi
  have hr3 : orderOf r=3 := hr.trans hp3
  exact ⟨v,hv,hvq,hv2,r,hrH,hr3,hi,
    normal_pair_core_eq d hA312 hH hU hn v r hv hvq hv2 hr3 hrH hi,
    hf.pair_star_symmetricThree d.third_index d.module_card
      (fun _ hk hi => source13_5_13_one d hA312 hH hU hk hi)
      (source_seed_centralizer_bound d hA312) r hrH hpair⟩

/-! The source witness can be consumed with its literal order, rather than a
separate upper-bound premise. This is the numerical input used by the
13.5.15 normal-pair elimination. -/

theorem source_normal_pair_core_card :
    ∃v∈V, v∉Source.QH H ∧ v^2=1 ∧
    ∃r∈H, orderOf r=3 ∧ v*r*v⁻¹=r⁻¹ ∧
      (V⊔V.map (MulAut.conj r).toMonoidHom).pCoreIn 2=Source.UH H V₃ ∧
      Nat.card (V⊔V.map (MulAut.conj r).toMonoidHom : Subgroup G)=192 ∧
      Nonempty (Source.starImage H (V⊔V.map (MulAut.conj r).toMonoidHom)≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨v,hv,hvq,hv2,r,hrH,hr,hi,hcore,hj⟩ :=
    source_normal_pair_core d hA312 hH hU hn
  exact ⟨v,hv,hvq,hv2,r,hrH,hr,hi,hcore,
    normal_pair_card_eq_192 d hA312 hH hU hn v r hv hvq hv2 hr hrH hi,hj⟩

/-- The source normal-pair consumer in quotient form: its literal quotient by
the quaternion two-core has order six. -/
theorem source_normal_pair_core_index :
    ∃v∈V, v∉Source.QH H ∧ v^2=1 ∧
    ∃r∈H, orderOf r=3 ∧ v*r*v⁻¹=r⁻¹ ∧
      (V⊔V.map (MulAut.conj r).toMonoidHom).pCoreIn 2=Source.UH H V₃ ∧
      ((Source.UH H V₃).subgroupOf
        (V⊔V.map (MulAut.conj r).toMonoidHom : Subgroup G)).index=6 ∧
      Nonempty (Source.starImage H (V⊔V.map (MulAut.conj r).toMonoidHom)≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨v,hv,hvq,hv2,r,hrH,hr,hi,hcore,hj⟩ :=
    source_normal_pair_core d hA312 hH hU hn
  exact ⟨v,hv,hvq,hv2,r,hrH,hr,hi,hcore,
    normal_pair_index_eq_six d hA312 hH hU hn v r hv hvq hv2 hr hrH hi,hj⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
