module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoFrameAlignment

/-!
# Selecting the first endpoint product within the aligned frame

Replacing t by tk also replaces the mixed Borel element v by k⁻¹vk.
These changes preserve both endpoint generating sets and every other frame
marking. The actual S₅ quotient selects one of these two frames, giving
order six for xt modulo the unchanged original first two-core. The same
outer involution still fixes d and z, inverts k, and has order-eight product
with the same q.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231.
This is the synchronized quotient-order step. The quaternion-centralizer
argument needed for order twelve in the original group remains separate.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations

private theorem left_twist_generates {A : Type*} [Group A] (k t q w : A)
    (h : closure (Set.range ![k,t,q,w])=⊤) :
    closure (Set.range ![k,t*k,q,w])=⊤ := by
  let C := closure (Set.range ![k,t*k,q,w])
  have hc (i : Fin 4) : ![k,t*k,q,w] i∈C := subset_closure ⟨i,rfl⟩
  apply top_unique
  rw [←h]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact hc 0
  · change t∈C
    have hh : (t*k)*k⁻¹∈C := C.mul_mem (hc 1) (C.inv_mem (hc 0))
    simpa only [mul_inv_cancel_right] using hh
  · exact hc 2
  · exact hc 3

private theorem right_twist_generates {A : Type*} [Group A] (k d z v q : A)
    (h : closure (Set.range ![k,d,z,v,q])=⊤) :
    closure (Set.range ![k,d,z,k⁻¹*v*k,q])=⊤ := by
  let C := closure (Set.range ![k,d,z,k⁻¹*v*k,q])
  have hc (i : Fin 5) : ![k,d,z,k⁻¹*v*k,q] i∈C := subset_closure ⟨i,rfl⟩
  apply top_unique
  rw [←h]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · change v∈C
    have hh : k*(k⁻¹*v*k)*k⁻¹∈C :=
      C.mul_mem (C.mul_mem (hc 0) (hc 3)) (C.inv_mem (hc 0))
    have he : k*(k⁻¹*v*k)*k⁻¹=v := by group
    rwa [he] at hh
  · exact hc 4

/-- Replacing t by tk preserves both endpoint generating sets when the
mixed Borel word is conjugated by k at the same time. -/
public noncomputable def Frame.twistT
    {R B P : Type*} [Group R] [Group B] [Group P]
    {A : RankTwoAmalgam R B P} (F : Frame A) : Frame A where
  k := F.k
  z := F.z
  q := F.q
  u := F.u
  v := F.k⁻¹*F.v*F.k
  w := F.w
  d := F.d
  t := F.t*A.left F.k
  k_order := F.k_order
  d_order := F.d_order
  z_order := F.z_order
  q_order := F.q_order
  t_square := by
    calc
      (F.t*A.left F.k)^2=(F.t*A.left F.k*F.t⁻¹)*(F.t^2)*A.left F.k := by
        simp only [pow_two]
        group
      _=1 := by rw [F.t_inverts,F.t_square]; simp
  t_outside := by
    intro hh
    have hh' := A.left.range.mul_mem hh (A.left.range.inv_mem ⟨F.k,rfl⟩)
    exact F.t_outside (by simpa only [mul_inv_cancel_right] using hh')
  t_inverts := by
    calc
      (F.t*A.left F.k)*A.left F.k*(F.t*A.left F.k)⁻¹=
          F.t*A.left F.k*F.t⁻¹ := by group
      _=(A.left F.k)⁻¹ := F.t_inverts
  d_commutes := F.d_commutes
  u_relation := F.u_relation
  v_relation := by
    rw [map_mul,map_mul,map_inv,F.v_relation]
    group
  w_relation := F.w_relation
  q_commutator := F.q_commutator
  z_core := F.z_core
  z_central := F.z_central
  left_generate := left_twist_generates _ _ _ _ F.left_generate
  right_generate := by
    simpa only [map_mul,map_inv] using right_twist_generates _ _ _ _ _ F.right_generate

@[simp] public theorem Frame.twistT_k {R B P : Type*} [Group R] [Group B] [Group P]
    {A : RankTwoAmalgam R B P} (F : Frame A) : F.twistT.k=F.k := by rfl
@[simp] public theorem Frame.twistT_z {R B P : Type*} [Group R] [Group B] [Group P]
    {A : RankTwoAmalgam R B P} (F : Frame A) : F.twistT.z=F.z := by rfl
@[simp] public theorem Frame.twistT_q {R B P : Type*} [Group R] [Group B] [Group P]
    {A : RankTwoAmalgam R B P} (F : Frame A) : F.twistT.q=F.q := by rfl
@[simp] public theorem Frame.twistT_d {R B P : Type*} [Group R] [Group B] [Group P]
    {A : RankTwoAmalgam R B P} (F : Frame A) : F.twistT.d=F.d := by rfl
@[simp] public theorem Frame.twistT_t {R B P : Type*} [Group R] [Group B] [Group P]
    {A : RankTwoAmalgam R B P} (F : Frame A) : F.twistT.t=F.t*A.left F.k := by rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations

namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open Subgroup Theory.GroupTheory SuzukiContainment GreenBook GeneratorRelations

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Select t or tk inside the same reduced frame. The adjusted mixed word
preserves both endpoint generating sets and leaves k,d,z,q unchanged. The
product has order six in the literal original first-core quotient. -/
public theorem original_frame_product_six_choice
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (hne : S≠reducedSylow L S)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
      (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
      (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (x : commonBorel L S) (hxN : (x:G)∉commonBorel L (reducedSylow L S))
    (hxk : (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹) :
    ∃ F' : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
      (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
      (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)),
      (F'=F ∨ F'=F.twistT) ∧ F'.k=F.k ∧ F'.d=F.d ∧ F'.z=F.z ∧ F'.q=F.q ∧
      orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i))
        (inclusion (commonBorel_le_parabolic i) x*
          inclusion (reduced_parabolic_le h i) F'.t))=6 := by
  let P := parabolic L S i
  let ki : P := ⟨F.k, reduced_parabolic_le h i (commonBorel_le_parabolic i F.k.property)⟩
  let xi : P := inclusion (commonBorel_le_parabolic i) x
  let ti : P := inclusion (reduced_parabolic_le h i) F.t
  obtain ⟨d⟩ := original_first_quotient_of_ne h i e hne
  let q := QuotientGroup.mk' (pCore 2 P)
  let v := d.toMonoidHom.comp q
  have hki : orderOf ki=3 := (orderOf_coe ki).symm.trans ((orderOf_coe F.k).trans F.k_order)
  have hk3 : ki^3=1 := by rw [←hki,pow_orderOf_eq_one]
  have hvk : orderOf (v ki)=3 := by
    apply orderOf_eq_prime
    · rw [←map_pow,hk3,map_one]
    · intro he
      have hq : q ki=1 := d.injective (he.trans d.map_one.symm)
      have hkQ : ki∈pCore 2 P := (QuotientGroup.eq_one_iff _).mp hq
      have hd := _root_.orderOf_dvd_natCard (x:=(⟨ki,hkQ⟩:pCore 2 P))
      rw [←orderOf_coe,hki,original_core_card h i e] at hd
      norm_num at hd
  have hxodd : v xi∉alternatingGroup (Fin 5) := by
    intro he
    have hxR := (original_first_quotient_reduced h i e hne d xi).mp he
    apply hxN
    rw [←reduced_parabolic_inf_borel h i]
    exact ⟨hxR,x.property⟩
  have hteven : v ti∈alternatingGroup (Fin 5) :=
    (original_first_quotient_reduced h i e hne d ti).mpr F.t.property
  have hxi : xi*ki*xi⁻¹=ki⁻¹ := Subtype.ext hxk
  have hti : ti*ki*ti⁻¹=ki⁻¹ := by
    apply Subtype.ext
    exact congrArg (fun y : parabolic L (reducedSylow L S) i => (y:G)) F.t_inverts
  have hti2 : ti^2=1 := by
    simpa only [map_pow,map_one] using congrArg (inclusion (reduced_parabolic_le h i)) F.t_square
  obtain ⟨u,hu,_,_,hu6⟩ := select_product_six v ki xi ti hvk hxodd hteven hxi hti2 hti
  rcases hu with rfl | rfl
  · exact ⟨F,Or.inl rfl,rfl,rfl,rfl,rfl,(d.orderOf_eq (q (xi*ti))).symm.trans hu6⟩
  · refine ⟨F.twistT,Or.inr rfl,rfl,rfl,rfl,rfl,?_⟩
    exact (d.orderOf_eq (q (xi*(ti*ki)))).symm.trans hu6

public theorem original_frame_product_six
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (hne : S≠reducedSylow L S)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
      (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
      (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (x : commonBorel L S) (hxN : (x:G)∉commonBorel L (reducedSylow L S))
    (hxk : (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹) :
    ∃ F' : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
      (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
      (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)),
      F'.k=F.k ∧ F'.d=F.d ∧ F'.z=F.z ∧ F'.q=F.q ∧
      orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i))
        (inclusion (commonBorel_le_parabolic i) x*
          inclusion (reduced_parabolic_le h i) F'.t))=6 := by
  obtain ⟨F',_,hk,hd,hz,hq,ho⟩ := original_frame_product_six_choice h i j e hne F x hxN hxk
  exact ⟨F',hk,hd,hz,hq,ho⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo

namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open Subgroup Theory.GroupTheory SuzukiContainment GreenBook GeneratorRelations
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- One frame simultaneously has all outer action relations, the order-eight
quaternion product, and order six for xt in the original first-core quotient.
The adjustment of t also adjusts its mixed Borel word and retains both complete
endpoint generating sets. This does not assert order twelve before quotienting. -/
public theorem original_aligned_frame_product
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S) :
    ∃ F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)),
      ∃ x : commonBorel L S,
      F.d=reducedCubic j e.right ∧ F.k*F.z=F.z*F.k ∧
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹ ∧
      (x:G)*(F.d:G)=(F.d:G)*(x:G) ∧
      (x:G)*(F.z:G)=(F.z:G)*(x:G) ∧ orderOf ((x:G)*(F.q:G))=8 ∧
      orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i))
        (inclusion (commonBorel_le_parabolic i) x*
          inclusion (reduced_parabolic_le h i) F.t))=6 ∧
      IsComplement' ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
        (zpowers x) ∧
      ∀ r : Fin 2, IsComplement'
        ((parabolic L (reducedSylow L S) r).subgroupOf (parabolic L S r))
        (zpowers (inclusion (commonBorel_le_parabolic r) x)) := by
  obtain ⟨F,x,hd,hkz,hx,hxN,hxk,hxd,hxz,hxq,hB,hP⟩ :=
    original_aligned_quaternion_frame h i j e hne
  obtain ⟨F',hk,hd',hz,hq,h6⟩ := original_frame_product_six h i j e.left hne F x hxN hxk
  refine ⟨F',x,hd'.trans hd,?_,hx,hxN,?_,?_,?_,?_,h6,hB,hP⟩
  · rwa [hk,hz]
  · rwa [hk]
  · rwa [hd']
  · rwa [hz]
  · rwa [hq]

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
