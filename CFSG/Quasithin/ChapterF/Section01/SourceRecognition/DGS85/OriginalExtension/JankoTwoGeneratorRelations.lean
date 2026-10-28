module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoQuaternionOrbit

/-!
# Compatible generators for the reduced Hall–Janko endpoints

Short checked words recover every generator of the actual second core
and its normalizer, and every generator of the actual common Sylow in the
first endpoint. The reduced Borel has prime index five in the first
endpoint; the chosen cubic inverter lies outside that entire Borel.
Together these prove both endpoint-generation statements of DGS (15.3).

The witnesses retain q in the actual cubic commutator of the first core,
z in the center of the second core, and the intermediate Borel elements
z^d, z^(dt), and q^d. Their transport requires both commuting inclusion
squares of an amalgam isomorphism. No compatibility is inferred from
three independent parabolic equivalences.

Source: DGS, Groups and Graphs (1985), (15.3)(iv)–(vi), printed p.229.
The word witnesses use the retained ATLAS J2G1-p100B0 permutations and
the existing CFSG radical/Sylow enumerations. Every word identity is
checked by Lean's kernel. The compact table for z avoids repeated
expansion of its original long word. The outer-action and order-twelve
relations on pp.230–231 are not asserted here.
-/

open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer GeneratorPair GeneratorPair.SecondOrbitCertificate
open FirstParabolic

namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations

/-- The source endpoint generators, including the three intermediate
Borel elements needed to transport the mixed word z^(dt). -/
public structure Frame {R B P : Type*} [Group R] [Group B] [Group P]
    (A : RankTwoAmalgam R B P) where
  k : B
  z : B
  q : B
  u : B
  v : B
  w : B
  d : P
  t : R
  k_order : orderOf k=3
  d_order : orderOf d=3
  z_order : orderOf z=2
  q_order : orderOf q=4
  t_square : t^2=1
  t_outside : t∉A.left.range
  t_inverts : t*A.left k*t⁻¹=(A.left k)⁻¹
  d_commutes : d*A.right k=A.right k*d
  u_relation : A.right u=d⁻¹*A.right z*d
  v_relation : A.left v=t⁻¹*A.left u*t
  w_relation : A.right w=d⁻¹*A.right q*d
  q_commutator : A.left q∈⁅pCore 2 R,zpowers (A.left k)⁆
  z_core : A.right z∈pCore 2 P
  z_central : ∀ a∈pCore 2 P,A.right z*a=a*A.right z
  left_generate : closure (Set.range ![A.left k,t,A.left q,A.left w])=⊤
  right_generate : closure (Set.range ![A.right k,d,A.right z,A.right v,A.right q])=⊤

private theorem map_generators {R P : Type*} [Group R] [Group P]
    {n : ℕ} (f : R ≃* P) (a : Fin n → R) (b : Fin n → P)
    (hb : ∀ i,b i=f (a i)) (ha : closure (Set.range a)=⊤) :
    closure (Set.range b)=⊤ := by
  have he : Set.range b=f '' Set.range a := by
    rw [←Set.range_comp]
    congr 1
    exact funext hb
  rw [he,←MonoidHom.coe_coe,←MonoidHom.map_closure,ha]
  exact Subgroup.map_top_of_surjective f.toMonoidHom f.surjective

/-- Compatible overlap maps transport the same endpoint relations and
both generating sets, including the literal core and mixed Borel words. -/
public noncomputable def Frame.map
    {R B P R' B' P' : Type*} [Group R] [Group B] [Group P]
    [Group R'] [Group B'] [Group P']
    {A : RankTwoAmalgam R B P} {A' : RankTwoAmalgam R' B' P'}
    (F : Frame A) (e : RankTwoAmalgam.Iso A A') : Frame A' where
  k := e.middle F.k
  z := e.middle F.z
  q := e.middle F.q
  u := e.middle F.u
  v := e.middle F.v
  w := e.middle F.w
  d := e.right F.d
  t := e.left F.t
  k_order := (e.middle.orderOf_eq _).trans F.k_order
  d_order := (e.right.orderOf_eq _).trans F.d_order
  z_order := (e.middle.orderOf_eq _).trans F.z_order
  q_order := (e.middle.orderOf_eq _).trans F.q_order
  t_square := by rw [←map_pow,F.t_square,map_one]
  t_outside := by
    rintro ⟨b,hb⟩
    apply F.t_outside
    refine ⟨e.middle.symm b,e.left.injective ?_⟩
    rw [e.left_commutes,e.middle.apply_symm_apply]
    exact hb
  t_inverts := by
    simpa only [map_mul,map_inv,e.left_commutes] using congrArg e.left F.t_inverts
  d_commutes := by
    simpa only [map_mul,e.right_commutes] using congrArg e.right F.d_commutes
  u_relation := by
    simpa only [map_mul,map_inv,e.right_commutes] using congrArg e.right F.u_relation
  v_relation := by
    simpa only [map_mul,map_inv,e.left_commutes] using congrArg e.left F.v_relation
  w_relation := by
    simpa only [map_mul,map_inv,e.right_commutes] using congrArg e.right F.w_relation
  q_commutator := by
    have hh := mem_map_of_mem e.left.toMonoidHom F.q_commutator
    rw [map_commutator,pCore_map_iso,MonoidHom.map_zpowers] at hh
    simpa only [MulEquiv.coe_toMonoidHom,e.left_commutes] using hh
  z_core := by
    rw [←pCore_map_iso 2 e.right,←e.right_commutes]
    exact mem_map_of_mem e.right.toMonoidHom F.z_core
  z_central := by
    intro a ha
    rw [←pCore_map_iso 2 e.right] at ha
    obtain ⟨a,ha,rfl⟩ := ha
    simpa only [map_mul,e.right_commutes,MulEquiv.coe_toMonoidHom] using congrArg e.right (F.z_central a ha)
  left_generate := map_generators e.left _ _ (by intro i; fin_cases i <;>
    first | exact (e.left_commutes _).symm | rfl) F.left_generate
  right_generate := map_generators e.right _ _ (by intro i; fin_cases i <;>
    first | exact (e.right_commutes _).symm | rfl) F.right_generate


section
variable {R B P R' B' P' : Type*} [Group R] [Group B] [Group P]
  [Group R'] [Group B'] [Group P']
  {A : RankTwoAmalgam R B P} {A' : RankTwoAmalgam R' B' P'}
  (F : Frame A) (e : RankTwoAmalgam.Iso A A')

@[simp] public theorem Frame.map_k : (F.map e).k=e.middle F.k := by rfl
@[simp] public theorem Frame.map_z : (F.map e).z=e.middle F.z := by rfl
@[simp] public theorem Frame.map_q : (F.map e).q=e.middle F.q := by rfl
@[simp] public theorem Frame.map_d : (F.map e).d=e.right F.d := by rfl
@[simp] public theorem Frame.map_t : (F.map e).t=e.left F.t := by rfl
end

/-- The order-four elements in the moved first-core factor are the cubic
conjugates of the frame's q and its inverse. -/
@[expose] public def Frame.QuaternionOrbit
    {R B P : Type*} [Group R] [Group B] [Group P]
    {A : RankTwoAmalgam R B P} (F : Frame A) : Prop :=
  ∀ y : R,y∈⁅pCore 2 R,zpowers (A.left F.k)⁆ → orderOf y=4 →
    ∃ n : Fin 3,
      y=(A.left F.k)^n.val*A.left F.q*((A.left F.k)^n.val)⁻¹ ∨
      y=(A.left F.k)^n.val*(A.left F.q)⁻¹*((A.left F.k)^n.val)⁻¹

/-- Both inclusion squares preserve the moved quaternion orbit. -/
public theorem Frame.quaternionOrbit_map
    {R B P R' B' P' : Type*} [Group R] [Group B] [Group P]
    [Group R'] [Group B'] [Group P']
    {A : RankTwoAmalgam R B P} {A' : RankTwoAmalgam R' B' P'}
    (F : Frame A) (e : RankTwoAmalgam.Iso A A') (hF : F.QuaternionOrbit) :
    (F.map e).QuaternionOrbit := by
  intro y hy ho
  have hm : e.left.symm y∈⁅pCore 2 R,zpowers (A.left F.k)⁆ := by
    have hh := mem_map_of_mem e.left.symm.toMonoidHom hy
    rw [map_commutator,pCore_map_iso,MonoidHom.map_zpowers] at hh
    have he : e.left.symm (A'.left (F.map e).k)=A.left F.k := by
      change e.left.symm (A'.left (e.middle F.k))=A.left F.k
      rw [←e.left_commutes,e.left.symm_apply_apply]
    simpa only [MulEquiv.coe_toMonoidHom,he] using hh
  obtain ⟨n,hn⟩ := hF (e.left.symm y) hm ((e.left.symm.orderOf_eq y).trans ho)
  refine ⟨n,?_⟩
  rw [Frame.map_k,Frame.map_q]
  rcases hn with hn | hn
  · apply Or.inl
    simpa only [map_mul,map_inv,map_pow,e.left.apply_symm_apply,e.left_commutes]
      using congrArg e.left hn
  · apply Or.inr
    simpa only [map_mul,map_inv,map_pow,e.left.apply_symm_apply,e.left_commutes]
      using congrArg e.left hn

private def tWord : List (Fin 3) := [2,2,0,1,0,2,2,2,2,2,2,0,2,0,2,0,2,0,1,0,2,2,0,1,0,1,0,2,0,2,0]
private def t : Carrier := localWord tWord
private def tMap : Fin 100 → Fin 100 := packedMap 3881624724470476115528354446615250408763469728990278980862273442714448688269640655557939205451083296245890251434252628308280335810936193140659017801965556861039639078195667381313023073821921928529120070066492882
private theorem tMap_sq : ∀ i, tMap (tMap i)=i := by apply allFin; decide +kernel
private def tPerm : Equiv.Perm (Fin 100) := tablePerm tMap tMap tMap_sq tMap_sq
private theorem inclusion_word (w : List (Fin 3)) :
    inclusion (localWord w)=evalWord ![tableA,tableB,tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a,b,b⁻¹] i*localWord w)=_
    rw [map_mul,ih]
    congr 1
    fin_cases i <;> simp [a,b,Sporadic.LeechRelated.J2.inclusion,generatorA_eq_table,generatorB_eq_table]
private theorem t_inclusion : inclusion t=tPerm := by
  rw [t,inclusion_word]
  apply Equiv.ext
  apply allFin
  decide +kernel

private def k : Carrier := oddGenerator 1
private def d : Carrier := oddGenerator 0
private def q : Carrier := radicalElement 12
private def u : Carrier := sElement 5
private def v : Carrier := sElement 116
private def w : Carrier := sElement 47
private def alpha : Fin 5 → Carrier := ![k,d,z,v,q]
private def beta : Fin 4 → Carrier := ![k,t,q,w]
private theorem z_s : z=sElement 6 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [show inclusion z=FirstFusion.tPerm from FirstFusion.inclusion_t,sElement_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem z_inclusion : inclusion z=SylowData.sTable 6 :=
  (congrArg inclusion z_s).trans (sElement_inclusion 6)
private def alphaTable : Fin 5 → Equiv.Perm (Fin 100) :=
  ![QuotientData.oddTable 1,QuotientData.oddTable 0,SylowData.sTable 6,
    SylowData.sTable 116,RadicalStructureData.tablePerm 12]
private def betaTable : Fin 4 → Equiv.Perm (Fin 100) :=
  ![QuotientData.oddTable 1,tPerm,RadicalStructureData.tablePerm 12,SylowData.sTable 47]
private theorem alpha_inclusion (i : Fin 5) : inclusion (alpha i)=alphaTable i := by
  fin_cases i
  · exact oddGenerator_inclusion 1
  · exact oddGenerator_inclusion 0
  · exact z_inclusion
  · exact sElement_inclusion 116
  · exact radicalElement_inclusion 12
private theorem beta_inclusion (i : Fin 4) : inclusion (beta i)=betaTable i := by
  fin_cases i
  · exact oddGenerator_inclusion 1
  · exact t_inclusion
  · exact radicalElement_inclusion 12
  · exact sElement_inclusion 47
private theorem eval_inclusion {n : ℕ} (g : Fin n → Carrier)
    (gs : Fin n → Equiv.Perm (Fin 100)) (hg : ∀ i,inclusion (g i)=gs i)
    (a : List (Fin n)) : inclusion (evalWord g a)=evalWord gs a := by
  induction a with
  | nil => rfl
  | cons i a ih => exact (map_mul inclusion _ _).trans (congrArg₂ (·*·) (hg i) ih)
private theorem word_mem {A : Type*} [Group A] {n : ℕ} (g : Fin n → A)
    (H : Subgroup A) (hg : ∀ i,g i∈H) (a : List (Fin n)) : evalWord g a∈H := by
  induction a with
  | nil => exact H.one_mem
  | cons i a ih => exact H.mul_mem (hg i) ih
private theorem letters_mem {A : Type*} [Group A] {n : ℕ} (g : Fin n → A) (i : Fin n) :
    g i ∈ closure (Set.range g) := subset_closure ⟨i,rfl⟩

private def alphaQWords : Fin 6 → List (Fin 5) := ![[1, 0, 0, 4, 1, 0, 4, 1], [4, 1, 1, 0, 0, 4, 1, 0], [0, 4, 1, 2, 1, 1, 0, 0], [4, 1, 2, 1, 1], [1, 1, 2, 1], [2]]
private def alphaNWords : Fin 3 → List (Fin 5) := ![[4, 0, 4, 1, 3, 1, 0, 0], [1], [0]]
private def betaSWords : Fin 7 → List (Fin 4) := ![[3, 3, 2], [2, 0, 0, 3, 0], [2, 0, 3, 2, 0, 0], [3, 1, 3, 3, 2, 1, 3], [0, 0, 2, 0], [1, 3, 3, 1, 3, 3, 2], [2, 2]]
private theorem alphaQ_check : ∀ i a,
    evalWord alphaTable (alphaQWords i) a=RadicalData.qGenTable i a := by
  intro i
  fin_cases i <;> apply allFin <;> decide +kernel
private theorem alphaN_check : ∀ i a,
    evalWord alphaTable (alphaNWords i) a=
      (![SylowData.sGenTable 3,QuotientData.oddTable 0,QuotientData.oddTable 1] i) a := by
  intro i
  fin_cases i <;> apply allFin <;> decide +kernel
private theorem betaS_check : ∀ i a,
    evalWord betaTable (betaSWords i) a=SylowData.sGenTable i a := by
  intro i
  fin_cases i <;> apply allFin <;> decide +kernel
private theorem alphaQ_eq (i : Fin 6) : evalWord alpha (alphaQWords i)=q₂Generator i := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [eval_inclusion alpha alphaTable alpha_inclusion,q₂Generator_inclusion]
  exact Equiv.ext (alphaQ_check i)
private theorem alphaN_eq (i : Fin 3) : evalWord alpha (alphaNWords i)=normalizerGenerator i := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [eval_inclusion alpha alphaTable alpha_inclusion]
  have hi : inclusion (normalizerGenerator i)=
      ![SylowData.sGenTable 3,QuotientData.oddTable 0,QuotientData.oddTable 1] i := by
    fin_cases i
    · exact sGenerator_inclusion 3
    · exact oddGenerator_inclusion 0
    · exact oddGenerator_inclusion 1
  rw [hi]
  exact Equiv.ext (alphaN_check i)
private theorem betaS_eq (i : Fin 7) : evalWord beta (betaSWords i)=sGenerator i := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [eval_inclusion beta betaTable beta_inclusion,sGenerator_inclusion]
  exact Equiv.ext (betaS_check i)

private theorem q_s : q=sElement 42 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [q,radicalElement_inclusion,sElement_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem t_mem : t∈l₁ := by
  apply mem_centralizer_singleton_iff.mpr
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,t_inclusion,z_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem t_sq : t^2=1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow,map_one,t_inclusion]
  exact Equiv.ext tMap_sq
private theorem t_inverts : t*k*t⁻¹=k⁻¹ := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_inv,map_inv,t_inclusion,k,oddGenerator_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem t_escape_check : ∀ i : Fin 128,
    (SylowData.sTable i 0,SylowData.sTable i 1) ≠ ((84 : Fin 100),(6 : Fin 100)) := by
  apply allFin
  decide +kernel
private theorem conjugate_mem {A : Type*} [Group A] (H : Subgroup A) (x y : A)
    (hx : x∈normalizer (H:Set A)) (hy : y∈H) : x*y*x⁻¹∈H :=
  (mem_normalizer_iff.mp hx y).mp hy
private theorem t_not_B : t∉SecondParabolic.Overlap.B := by
  intro ht
  have hn := SecondParabolic.Overlap.B_le_normalizer ht
  have hg : sGenerator 1∈s := subset_closure ⟨1,rfl⟩
  have hs := conjugate_mem s t (sGenerator 1) hn hg
  obtain ⟨i,hi⟩ := exists_sElement hs
  have hh := congrArg inclusion hi
  rw [sElement_inclusion,map_mul,map_mul,map_inv,t_inclusion,sGenerator_inclusion] at hh
  apply t_escape_check i
  exact (congrArg (fun f : Equiv.Perm (Fin 100) => (f 0,f 1)) hh).trans (by decide +kernel)

private theorem k_B : k∈SecondParabolic.Overlap.B :=
  (show zpowers k≤SecondParabolic.Overlap.B from le_sup_right) (mem_zpowers k)
private theorem z_B : z∈SecondParabolic.Overlap.B := (show s≤SecondParabolic.Overlap.B from le_sup_left) (z_s.symm ▸ sElement_mem 6)
private theorem q_B : q∈SecondParabolic.Overlap.B := (show s≤SecondParabolic.Overlap.B from le_sup_left) (q_s.symm ▸ sElement_mem 42)
private theorem u_B : u∈SecondParabolic.Overlap.B := (show s≤SecondParabolic.Overlap.B from le_sup_left) (sElement_mem 5)
private theorem v_B : v∈SecondParabolic.Overlap.B := (show s≤SecondParabolic.Overlap.B from le_sup_left) (sElement_mem 116)
private theorem w_B : w∈SecondParabolic.Overlap.B := (show s≤SecondParabolic.Overlap.B from le_sup_left) (sElement_mem 47)

private theorem alpha_generate : closure (Set.range alpha)=p₂ := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact oddGenerator_mem_p₂ 1
    · exact oddGenerator_mem_p₂ 0
    · exact SecondParabolic.Overlap.B_le_p₂ z_B
    · exact SecondParabolic.Overlap.B_le_p₂ v_B
    · exact SecondParabolic.Overlap.B_le_p₂ q_B
  · rw [full_normalizer_eq_candidate]
    apply sup_le
    · apply (closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      rw [←alphaQ_eq]
      exact word_mem alpha _ (letters_mem alpha) _
    · apply (closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      rw [←alphaN_eq]
      exact word_mem alpha _ (letters_mem alpha) _

private theorem beta_generate : closure (Set.range beta)=l₁ := by
  have hs : s≤closure (Set.range beta) := by
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    rw [←betaS_eq]
    exact word_mem beta _ (letters_mem beta) _
  have hB : SecondParabolic.Overlap.B≤closure (Set.range beta) :=
    sup_le hs (zpowers_le.mpr (letters_mem beta 0))
  have hi : SecondParabolic.Overlap.B.relIndex l₁=5 := by
    have hh := (SecondParabolic.Overlap.B.subgroupOf l₁).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe SecondParabolic.Overlap.B_le_l₁).toEquiv,
      SecondParabolic.Overlap.card_B,card_l₁] at hh
    change (SecondParabolic.Overlap.B.subgroupOf l₁).index=5
    omega
  have he := sup_zpowers_eq_of_relIndex_prime SecondParabolic.Overlap.B_le_l₁
    (by decide : Nat.Prime 5) hi t_mem t_not_B
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact SecondParabolic.Overlap.B_le_l₁ k_B
    · exact t_mem
    · exact SecondParabolic.Overlap.B_le_l₁ q_B
    · exact SecondParabolic.Overlap.B_le_l₁ w_B
  · rw [←he]
    exact sup_le hB (zpowers_le.mpr (letters_mem beta 1))

private theorem d_order : orderOf d=3 := by
  apply orderOf_eq_prime
  · apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [map_pow,map_one,d,oddGenerator_inclusion]
    apply Equiv.ext
    apply allFin
    decide +kernel
  · intro he
    have hh := congrArg inclusion he
    rw [d,oddGenerator_inclusion,map_one] at hh
    exact (by decide +kernel : QuotientData.oddTable 0≠1) hh
private theorem q_order : orderOf q=4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (p:=2) (n:=1)
  · intro he
    have hh := congrArg inclusion he
    rw [map_pow,map_one,q,radicalElement_inclusion] at hh
    exact (by decide +kernel : (RadicalStructureData.tablePerm 12)^2≠1) hh
  · apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [map_pow,map_one,q,radicalElement_inclusion]
    apply Equiv.ext
    apply allFin
    decide +kernel
private theorem d_commutes : d*k=k*d := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,d,k,oddGenerator_inclusion,oddGenerator_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem u_relation : u=d⁻¹*z*d := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_inv,u,d,sElement_inclusion,oddGenerator_inclusion,
    z_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem v_relation : v=t⁻¹*u*t := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_inv,v,u,sElement_inclusion,sElement_inclusion,t_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem w_relation : w=d⁻¹*q*d := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_inv,w,d,q,sElement_inclusion,oddGenerator_inclusion,radicalElement_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem q_comm : q=radicalElement 2*k*(radicalElement 2)⁻¹*k⁻¹ := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_mul,map_inv,map_inv,q,k,radicalElement_inclusion,
    radicalElement_inclusion,oddGenerator_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem z_core_mem : z∈q₂ := by
  rw [z_s]
  exact qElement_mem 6
private theorem z_centralizes : ∀ a∈q₂,z*a=a*z := by
  have hg : ∀ i : Fin 6,z*q₂Generator i=q₂Generator i*z := by
    intro i
    apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [map_mul,map_mul,q₂Generator_inclusion,
      z_inclusion]
    have hh : ∀ i a, (SylowData.sTable 6*RadicalData.qGenTable i) a=
        (RadicalData.qGenTable i*SylowData.sTable 6) a := by
      intro i
      fin_cases i <;> apply allFin <;> decide +kernel
    exact Equiv.ext (hh i)
  have hle : q₂≤centralizer ({z}:Set Carrier) := by
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hg i).symm
  exact fun a ha => (mem_centralizer_singleton_iff.mp (hle ha)).symm

private theorem map_vec4 {A D : Type*} (f : A → D) (a b c d : A) :
    (fun i => f (![a,b,c,d] i))=![f a,f b,f c,f d] := by
  funext i
  fin_cases i <;> rfl
private theorem map_vec5 {A D : Type*} (f : A → D) (a b c d e : A) :
    (fun i => f (![a,b,c,d,e] i))=![f a,f b,f c,f d,f e] := by
  funext i
  fin_cases i <;> rfl

private theorem internal_generate {A : Type*} [Group A] (H : Subgroup A)
    {n : ℕ} (g : Fin n → H) (hg : closure (Set.range (fun i => (g i:A)))=H) :
    closure (Set.range g)=⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,H.range_subtype]
  exact hg

private def concreteAmalgam := RankTwoAmalgam.ofSubgroups l₁ SecondParabolic.Overlap.B p₂
  SecondParabolic.Overlap.B_le_l₁ SecondParabolic.Overlap.B_le_p₂

private theorem not_range_inclusion {A : Type*} [Group A]
    (B P : Subgroup A) (hBP : B≤P) (x : P) (hx : (x:A)∉B) :
    x∉(Subgroup.inclusion hBP).range := by
  rintro ⟨b,hb⟩
  apply hx
  have he : (b:A)=(x:A) := congrArg (fun a : P => (a:A)) hb
  exact he ▸ b.property

private noncomputable def concreteFrame : Frame concreteAmalgam where
  k := ⟨k,k_B⟩
  z := ⟨z,z_B⟩
  q := ⟨q,q_B⟩
  u := ⟨u,u_B⟩
  v := ⟨v,v_B⟩
  w := ⟨w,w_B⟩
  d := ⟨d,oddGenerator_mem_p₂ 0⟩
  t := ⟨t,t_mem⟩
  k_order := (orderOf_coe _).symm.trans SecondParabolic.Overlap.v_order
  d_order := (orderOf_coe _).symm.trans d_order
  z_order := (orderOf_coe _).symm.trans (orderOf_eq_prime z_sq z_ne_one)
  q_order := (orderOf_coe _).symm.trans q_order
  t_square := Subtype.ext t_sq
  t_outside := not_range_inclusion _ _ SecondParabolic.Overlap.B_le_l₁ ⟨t,t_mem⟩ t_not_B
  t_inverts := Subtype.ext t_inverts
  d_commutes := Subtype.ext d_commutes
  u_relation := Subtype.ext u_relation
  v_relation := Subtype.ext v_relation
  w_relation := Subtype.ext w_relation
  q_commutator := by
    let r : l₁ := ⟨radicalElement 2,radical_le_l₁ (radicalElement_mem 2)⟩
    have hr : r∈pCore 2 l₁ := by rw [l₁_core_eq]; exact radicalElement_mem 2
    have he : concreteAmalgam.left ⟨q,q_B⟩=
        r*concreteAmalgam.left ⟨k,k_B⟩*r⁻¹*(concreteAmalgam.left ⟨k,k_B⟩)⁻¹ := Subtype.ext q_comm
    rw [he]
    exact commutator_mem_commutator hr (mem_zpowers _)
  z_core := by rw [p₂_core_eq_q₂ SecondParabolic.l₂_core_card]; exact z_core_mem
  z_central := by
    intro a ha
    rw [p₂_core_eq_q₂ SecondParabolic.l₂_core_card] at ha
    exact Subtype.ext (z_centralizes a ha)
  left_generate := internal_generate l₁ _ (by rw [map_vec4]; exact beta_generate)
  right_generate := internal_generate p₂ _ (by rw [map_vec5]; exact alpha_generate)

private noncomputable def markingIso : RankTwoAmalgam.Iso concreteAmalgam
    GreenBook.HallJanko.j2Model.toMarking.amalgam where
  left := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_zero.symm
  middle := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_B.symm
  right := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_one.symm
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- The actual ATLAS pair has the source generators and both endpoint
relations. All elements and the entire Borel are the marked concrete ones. -/
public theorem model_frame : Nonempty (Frame GreenBook.HallJanko.j2Model.toMarking.amalgam) :=
  ⟨concreteFrame.map markingIso⟩

private theorem k_z : k*z=z*k := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,k,oddGenerator_inclusion,z_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem k_alpha_commutator (i : Fin 5) :
    k*alpha i*k⁻¹*(alpha i)⁻¹=qElement (![0,0,0,0,18] i) := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_mul,map_inv,map_inv,k,oddGenerator_inclusion,
    alpha_inclusion,qElement_inclusion]
  have hh : ∀ i a,
      (QuotientData.oddTable 1*alphaTable i*(QuotientData.oddTable 1)⁻¹*(alphaTable i)⁻¹) a=
        RadicalData.qTable (![0,0,0,0,18] i) a := by
    intro i
    fin_cases i <;> apply allFin <;> decide +kernel
  exact Equiv.ext (hh i)

private theorem concrete_k_quotient_central :
    QuotientGroup.mk' (pCore 2 p₂) (concreteAmalgam.right concreteFrame.k) ∈
      center (p₂ ⧸ pCore 2 p₂) := by
  let v := QuotientGroup.mk' (pCore 2 p₂)
  let gs : Fin 5 → p₂ := ![concreteAmalgam.right concreteFrame.k,concreteFrame.d,
    concreteAmalgam.right concreteFrame.z,concreteAmalgam.right concreteFrame.v,
    concreteAmalgam.right concreteFrame.q]
  have hgs (i : Fin 5) : (gs i : Carrier)=alpha i := by
    fin_cases i <;> rfl
  have hg : closure (Set.range (fun i => v (gs i)))=⊤ := by
    have hh := congrArg (Subgroup.map v) concreteFrame.right_generate
    rw [MonoidHom.map_closure,←Set.range_comp,
      Subgroup.map_top_of_surjective v (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  rw [center_eq_iInf hg]
  simp only [mem_iInf]
  rintro _ ⟨i,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  let a := concreteAmalgam.right concreteFrame.k
  have hc : a*gs i*a⁻¹*(gs i)⁻¹∈pCore 2 p₂ := by
    rw [p₂_core_eq_q₂ SecondParabolic.l₂_core_card]
    change (a:Carrier)*(gs i:Carrier)*(a:Carrier)⁻¹*(gs i:Carrier)⁻¹∈q₂
    rw [hgs,show (a:Carrier)=k from rfl]
    rw [k_alpha_commutator]
    exact qElement_mem _
  have hh := (QuotientGroup.eq_one_iff _).mpr hc
  change v (a*gs i*a⁻¹*(gs i)⁻¹)=1 at hh
  rw [map_mul,map_mul,map_mul,map_inv,map_inv] at hh
  exact (mul_inv_eq_one.mp hh |> mul_inv_eq_iff_eq_mul.mp)

private theorem concrete_quaternion_orbit : concreteFrame.QuaternionOrbit := by
  intro y hy ho
  have hh := mem_map_of_mem l₁.subtype hy
  rw [map_commutator,MonoidHom.map_zpowers,l₁_core_eq,
    map_subgroupOf_eq_of_le radical_le_l₁] at hh
  obtain ⟨n,hn⟩ := GeneratorRelations.Orbit.quaternion_orbit (y:Carrier) hh
    ((orderOf_coe y).trans ho)
  refine ⟨n,?_⟩
  rcases hn with hn | hn
  · exact Or.inl (Subtype.ext hn)
  · exact Or.inr (Subtype.ext hn)

/-- The same checked frame uses the designated fixed-point-free cubic.
Its Cartan generator fixes z and is central modulo the second core. The
order-four elements in its moved quaternion factor form the stated orbit. These
markings allow the original outer involution to be aligned with this frame. -/
public theorem model_frame_marked :
    ∃ F : Frame GreenBook.HallJanko.j2Model.toMarking.amalgam,
      F.d=(MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_one).symm
        ⟨oddGenerator 0,oddGenerator_mem_p₂ 0⟩ ∧
      F.k*F.z=F.z*F.k ∧
      QuotientGroup.mk' (pCore 2 (GreenBook.HallJanko.j2Model.toMarking.P 1))
        (GreenBook.HallJanko.j2Model.toMarking.amalgam.right F.k) ∈
          center (GreenBook.HallJanko.j2Model.toMarking.P 1 ⧸
            pCore 2 (GreenBook.HallJanko.j2Model.toMarking.P 1)) ∧
      F.QuaternionOrbit := by
  refine ⟨concreteFrame.map markingIso,rfl,?_,?_,
    concreteFrame.quaternionOrbit_map markingIso concrete_quaternion_orbit⟩
  · have hz : concreteFrame.k*concreteFrame.z=concreteFrame.z*concreteFrame.k :=
      Subtype.ext k_z
    exact (map_mul markingIso.middle _ _).symm.trans
      ((congrArg markingIso.middle hz).trans (map_mul markingIso.middle _ _))
  · let v := LocalCoreTransport.quotientEquiv 2 markingIso.right
    have hh := (Subgroup.centerCongr v ⟨_,concrete_k_quotient_central⟩).property
    change v (QuotientGroup.mk' _ (concreteAmalgam.right concreteFrame.k)) ∈ _ at hh
    change QuotientGroup.mk' _ (markingIso.right (concreteAmalgam.right concreteFrame.k)) ∈ _ at hh
    rw [markingIso.right_commutes] at hh
    exact hh

/-- Canonical coordinates retained for the paired endpoint action calculation. -/
public theorem model_frame_coordinates :
    ∃ F : Frame GreenBook.HallJanko.j2Model.toMarking.amalgam,
      F.d=(MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_one).symm
        ⟨oddGenerator 0,oddGenerator_mem_p₂ 0⟩ ∧
      F.k*F.z=F.z*F.k ∧
      QuotientGroup.mk' (pCore 2 (GreenBook.HallJanko.j2Model.toMarking.P 1))
        (GreenBook.HallJanko.j2Model.toMarking.amalgam.right F.k) ∈
          center (GreenBook.HallJanko.j2Model.toMarking.P 1 ⧸
            pCore 2 (GreenBook.HallJanko.j2Model.toMarking.P 1)) ∧
      F.QuaternionOrbit ∧
      (F.k:Carrier)=oddGenerator 1 ∧
      (F.z:Carrier)=z ∧
      (F.t:Carrier)=localWord [2,2,0,1,0,2,2,2,2,2,2,0,2,0,2,0,2,0,1,0,2,2,0,1,0,1,0,2,0,2,0] := by
  refine ⟨concreteFrame.map markingIso,rfl,?_,?_,
    concreteFrame.quaternionOrbit_map markingIso concrete_quaternion_orbit,rfl,rfl,rfl⟩
  · have hz : concreteFrame.k*concreteFrame.z=concreteFrame.z*concreteFrame.k :=
      Subtype.ext k_z
    exact (map_mul markingIso.middle _ _).symm.trans
      ((congrArg markingIso.middle hz).trans (map_mul markingIso.middle _ _))
  · let v := LocalCoreTransport.quotientEquiv 2 markingIso.right
    have hh := (Subgroup.centerCongr v ⟨_,concrete_k_quotient_central⟩).property
    change v (QuotientGroup.mk' _ (concreteAmalgam.right concreteFrame.k)) ∈ _ at hh
    change QuotientGroup.mk' _ (markingIso.right (concreteAmalgam.right concreteFrame.k)) ∈ _ at hh
    rw [markingIso.right_commutes] at hh
    exact hh

/-- The actual ATLAS frame, with every independent generator coordinate retained.
These coordinates are used to identify a compatible action on both endpoints. -/
public theorem atlas_frame_coordinates :
    ∃ F : Frame (RankTwoAmalgam.ofSubgroups l₁ SecondParabolic.Overlap.B p₂
      SecondParabolic.Overlap.B_le_l₁ SecondParabolic.Overlap.B_le_p₂),
      (F.k:Carrier)=oddGenerator 1 ∧ (F.d:Carrier)=oddGenerator 0 ∧
      (F.z:Carrier)=z ∧ (F.q:Carrier)=radicalElement 12 ∧
      (F.t:Carrier)=localWord [2,2,0,1,0,2,2,2,2,2,2,0,2,0,2,0,2,0,1,0,2,2,0,1,0,1,0,2,0,2,0] :=
  ⟨concreteFrame,rfl,rfl,rfl,rfl,rfl⟩

/-- Agreement on the five independent marked generators determines compatible
maps on both endpoints. The mixed Borel words supply the other generators. -/
public theorem Frame.compatible_hom_ext
    {R B P X : Type*} [Group R] [Group B] [Group P] [Group X]
    {A : RankTwoAmalgam R B P} (F : Frame A)
    (f₁ g₁ : R →* X) (f₂ g₂ : P →* X)
    (hf : ∀ b, f₁ (A.left b)=f₂ (A.right b))
    (hg : ∀ b, g₁ (A.left b)=g₂ (A.right b))
    (hk : f₁ (A.left F.k)=g₁ (A.left F.k))
    (ht : f₁ F.t=g₁ F.t) (hq : f₁ (A.left F.q)=g₁ (A.left F.q))
    (hd : f₂ F.d=g₂ F.d) (hz : f₂ (A.right F.z)=g₂ (A.right F.z)) :
    f₁=g₁ ∧ f₂=g₂ := by
  have hqR : f₂ (A.right F.q)=g₂ (A.right F.q) := by rw [←hf,←hg,hq]
  have hkR : f₂ (A.right F.k)=g₂ (A.right F.k) := by rw [←hf,←hg,hk]
  have hu : f₁ (A.left F.u)=g₁ (A.left F.u) := by
    rw [hf,hg,F.u_relation,map_mul,map_mul,map_inv,map_mul,map_mul,map_inv,hd,hz]
  have hv : f₂ (A.right F.v)=g₂ (A.right F.v) := by
    rw [←hf,←hg,F.v_relation,map_mul,map_mul,map_inv,map_mul,map_mul,map_inv,ht,hu]
  have hw : f₁ (A.left F.w)=g₁ (A.left F.w) := by
    rw [hf,hg,F.w_relation,map_mul,map_mul,map_inv,map_mul,map_mul,map_inv,hd,hqR]
  constructor
  · apply MonoidHom.eq_of_eqOn_dense F.left_generate
    rintro _ ⟨i,rfl⟩
    fin_cases i <;> first | exact hk | exact ht | exact hq | exact hw
  · apply MonoidHom.eq_of_eqOn_dense F.right_generate
    rintro _ ⟨i,rfl⟩
    fin_cases i <;> first | exact hkR | exact hd | exact hz | exact hv | exact hqR

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations
