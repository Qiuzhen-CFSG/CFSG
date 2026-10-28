module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EdgeAgreement
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.LocalSylow
public import Mathlib.GroupTheory.Index
/-!
# The actual central residual on the J4 line kernel

An automorphism of K fixing K∩H fixes R pointwise. Its displacement lies in
C_G(R)=Z. Average this crossed homomorphism over the seven cosets of K∩H:
the automorphism is conjugation by an element of Z centralizing K∩H.
Since K∩H contains the original extraspecial Q, this element lies in Z(H).
The residual is retained; conjugation by z is not incorrectly declared trivial.

A second odd-index argument detects two actions whose discrepancy has
exponent two and centralizes the first action. The plane--line group will
apply it at its index-five point stabilizer in KernelActions.

Source: Aschbacher--Segev (1991), final paragraph of section 8, pp.606--607;
the central-residual comparison underlying the cited (7.9.3).
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry SourceCycleBase GraphUniquenessSystem
open scoped IsMulCommutative Pointwise
private theorem crossed_principal_of_odd_index
    {J A : Type*} [Group J] [Finite J] [CommGroup A]
    (I : Subgroup J) (ρ : J →* MulAut A) (δ : J → A)
    (hmul : ∀ g k, δ (g*k)=δ g*ρ g (δ k))
    (hI : ∀ i ∈ I, δ i=1) (hpow : ∀ a : A, a^2=1) (hodd : Odd I.index) :
    ∃ c : A, (∀ i : I, ρ i c=c) ∧ ∀ g, δ g=c*(ρ g c)⁻¹ := by
  classical
  let := Fintype.ofFinite (J ⧸ I)
  let d : J ⧸ I → A := Quotient.lift δ (by
    intro a b hab
    have hh := hI (a⁻¹*b) (QuotientGroup.leftRel_apply.mp hab)
    have he := hmul a (a⁻¹*b)
    rw [mul_inv_cancel_left,hh,map_one,mul_one] at he
    exact he.symm)
  have hd (g : J) (q : J ⧸ I) : d (g • q)=δ g*ρ g (d q) := by
    induction q using QuotientGroup.induction_on with
    | H a => exact hmul g a
  let c : A := ∏ q : J ⧸ I, d q
  have hc (g : J) : c=δ g*ρ g c := by
    have hr : c=∏ q : J ⧸ I, d (g • q) :=
      (Fintype.prod_equiv (MulAction.toPerm g) (fun q => d (g • q)) d (fun _ => rfl)).symm
    conv_lhs => rw [hr]
    simp_rw [hd]
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←map_prod]
    have hp : δ g^Fintype.card (J ⧸ I)=δ g := by
      rw [←Nat.card_eq_fintype_card,←index_eq_card]
      obtain ⟨k,hk⟩ := hodd
      rw [hk,pow_add,pow_mul,hpow,one_pow,pow_one,one_mul]
    rw [hp]
  refine ⟨c,?_,fun g => (eq_mul_inv_iff_mul_eq).mpr (hc g).symm⟩
  intro i
  have hi := hc i
  rw [hI i i.property,one_mul] at hi
  exact hi.symm

/-- Odd-index averaging retains the possible inner correction in the
centralizer, rather than claiming that the automorphism is trivial. -/
theorem residual_inner_of_odd_index
    {J : Type*} [Group J] [Finite J]
    (R Z I : Subgroup J) [R.Normal] [Z.Normal] [IsMulCommutative Z]
    (hRI : R ≤ I) (hCZ : Subgroup.centralizer (R : Set J) ≤ Z)
    (hpow : ∀ c : Z, c^2=1) (hodd : Odd I.index)
    (f : MulAut J) (hf : ∀ i : I, f i=i) :
    ∃ c : Z, (c : J) ∈ Subgroup.centralizer (I : Set J) ∧ f=MulAut.conj (c : J) := by
  have hfix (i : J) (hi : i ∈ I) : f i=i := hf ⟨i,hi⟩
  have hδ (g : J) : f g*g⁻¹ ∈ Z := by
    apply hCZ
    apply mem_centralizer_iff.mpr
    intro r hr
    have hi : g⁻¹*r*g ∈ R := by
      simpa only [inv_inv] using (inferInstance : R.Normal).conj_mem r hr g⁻¹
    have he := hfix (g⁻¹*r*g) (hRI hi)
    rw [map_mul,map_mul,map_inv,hfix r (hRI hr)] at he
    have hh := congrArg (fun x => f g*x*g⁻¹) he
    group at hh
    simpa only [mul_assoc,zpow_neg_one] using hh
  let δ : J → Z := fun g => ⟨f g*g⁻¹,hδ g⟩
  obtain ⟨c,hc,he⟩ := crossed_principal_of_odd_index I
    (MulAut.conjNormal : J →* MulAut Z) δ
    (by intro g k; apply Subtype.ext; simp [δ,map_mul,mul_assoc])
    (by intro i hi; apply Subtype.ext; simp [δ,hfix i hi]) hpow hodd
  refine ⟨c,?_,?_⟩
  · apply mem_centralizer_iff.mpr
    intro i hi
    have hh := congrArg Subtype.val (hc ⟨i,hi⟩)
    exact mul_inv_eq_iff_eq_mul.mp hh
  · ext g
    have hh := congrArg Subtype.val (he g)
    change f g*g⁻¹=(c : J)*(g*(c : J)*g⁻¹)⁻¹ at hh
    calc
      f g = (f g*g⁻¹)*g := by group
      _ = ((c : J)*(g*(c : J)*g⁻¹)⁻¹)*g := by rw [hh]
      _ = MulAut.conj (c : J) g := by simp only [MulAut.conj_apply]; group

/-- An odd-index agreement subgroup detects two actions whose discrepancy
is central relative to the first action and has exponent two. -/
theorem hom_eq_of_odd_index_of_central_discrepancy
    {J A : Type*} [Group J] [Finite J] [Group A]
    (I : Subgroup J) (hodd : Odd I.index) (f g : J →* A)
    (hI : ∀ i : I, f i=g i)
    (hc : ∀ j k, Commute (g j*(f j)⁻¹) (f k))
    (hsq : ∀ j, (g j*(f j)⁻¹)^2=1) : f=g := by
  let δ : J →* A := {
    toFun := fun j => g j*(f j)⁻¹
    map_one' := by simp
    map_mul' := by
      intro j k
      have he := (hc k j).inv_right.eq
      calc
        g (j*k)*(f (j*k))⁻¹ = g j*(g k*(f k)⁻¹)*(f j)⁻¹ := by
          simp only [map_mul,mul_inv_rev]; group
        _ = g j*((f j)⁻¹*(g k*(f k)⁻¹)) := by rw [mul_assoc,he]
        _ = _ := by group }
  have hle : I ≤ δ.ker := by
    intro i hi
    change g i*(f i)⁻¹=1
    rw [hI ⟨i,hi⟩,mul_inv_cancel]
  have hdiv := index_dvd_of_le hle
  have hodd' : Odd δ.ker.index := by
    exact hodd.of_dvd_nat hdiv
  ext j
  have hp := δ.ker.pow_index_mem j
  change δ (j^δ.ker.index)=1 at hp
  rw [map_pow] at hp
  obtain ⟨n,hn⟩ := hodd'
  rw [hn,pow_add,pow_mul,show δ j^2=1 from hsq j,one_pow,pow_one,one_mul] at hp
  exact (mul_inv_eq_one.mp hp).symm

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

include h in
private theorem marker_ne : z ≠ 1 := by
  intro hz
  have hh := h.involution
  simp [hz] at hh

/-- K acts transitively on the seven nonidentity elements of the original Z. -/
theorem lineKernel_plane_index : ((centralizer z).subgroupOf a.d.K).index=7 := by
  classical
  let : MulAction a.d.K a.d.space := MulAction.compHom a.d.space a.d.KAction
  let z₀ : a.d.space := ⟨z,(a.d.markedPoint 0).property⟩
  have hz₀ : z₀ ≠ 1 := fun he => (marker_ne (h := h)) (congrArg Subtype.val he)
  have horbit : MulAction.orbit a.d.K z₀={v : a.d.space | v ≠ 1} := by
    ext v
    constructor
    · rintro ⟨k,hk⟩ hv
      exact hz₀ ((a.d.KAction k).injective (hk.trans (hv.trans (map_one _).symm)))
    · intro hv
      obtain ⟨n,hn,he⟩ := a.d.normalizer_transitive v.val v.property
        (fun he => hv (Subtype.ext he))
      obtain ⟨k,hk⟩ := a.d.KAction_surjective h (a.d.normalizerAction ⟨n,hn⟩)
      refine ⟨k,?_⟩
      change a.d.KAction k z₀=v
      rw [hk]
      exact Subtype.ext he
  have hstab : MulAction.stabilizer a.d.K z₀=(centralizer z).subgroupOf a.d.K := by
    ext k
    change a.d.KAction k z₀=z₀ ↔ (k : G) ∈ centralizer z
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hk
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hk)
    · intro hk
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hk)
  rw [←hstab,MulAction.index_stabilizer,horbit,←Nat.card_coe_set_eq]
  let := Fintype.ofFinite a.d.space
  change Nat.card {v : a.d.space // v ≠ 1}=7
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique,←Nat.card_eq_fintype_card,show Nat.card a.d.space=8 from a.d.card]

/-- The actual residual automorphism on K is conjugation by an element of
Z(H), with the original central involution retained. -/
theorem lineKernel_residual_inner
    (f : MulAut a.d.K) (hf : ∀ k : (centralizer z).subgroupOf a.d.K, f k=k) :
    ∃ c : a.d.K, (c : G) ∈ (center (centralizer z)).map (centralizer z).subtype ∧
      f=MulAut.conj c := by
  let R := a.d.R.subgroupOf a.d.K
  let Z := a.d.space.subgroupOf a.d.K
  let I := (centralizer z).subgroupOf a.d.K
  let : R.Normal := a.d.R_normal_in_K
  let : Z.Normal := (normal_subgroupOf_iff_le_normalizer
    ((a.d.space_le_R h).trans inf_le_left)).mpr a.d.K_le_normalizer
  let : IsElementaryAbelian 2 a.d.space := a.d.elementary
  let : IsMulCommutative Z := ⟨⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val*y.val.val=y.val.val*x.val.val
    exact congrArg Subtype.val (mul_comm (⟨x.val.val,x.property⟩ : a.d.space)
      (⟨y.val.val,y.property⟩ : a.d.space))⟩⟩
  have hRI : R ≤ I := fun k hk => a.d.S_le_point_centralizer (a.d.markedPoint 0).property hk.2
  have hCZ : Subgroup.centralizer (R : Set a.d.K) ≤ Z := by
    intro k hk
    change (k : G) ∈ a.d.space
    rw [←a.d.R_centralizer h]
    apply mem_centralizer_iff.mpr
    intro r hr
    have he := mem_centralizer_iff.mp hk ⟨r,hr.1⟩ hr
    exact congrArg Subtype.val he
  have hpow (c : Z) : c^2=1 := by
    apply Subtype.ext
    apply Subtype.ext
    have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 a.d.space) (⟨c.val.val,c.property⟩ : a.d.space)
    change c.val.val^2=1
    exact congrArg Subtype.val he
  obtain ⟨c,hc,hf⟩ := residual_inner_of_odd_index R Z I hRI hCZ hpow
    (by rw [show I.index=7 from lineKernel_plane_index a]; decide) f hf
  have hcH : (c.val : G) ∈ centralizer z :=
    a.d.S_le_point_centralizer (a.d.markedPoint 0).property ((a.d.space_le_R h c.property).2)
  let cH : centralizer z := ⟨c.val,hcH⟩
  have hcZ : cH ∈ center (centralizer z) := by
    rw [←planeCoreAction_ker h]
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    apply Subtype.ext
    have hqK : q.val.val ∈ a.d.K :=
      core_le_threeSpaceCores a.d.space (a.d.markedPoint 0).property ((marker_ne (h := h)))
        (mem_map_of_mem (centralizer z).subtype q.property)
    have he := mem_centralizer_iff.mp hc ⟨q.val.val,hqK⟩ q.val.property
    have he' : q.val.val*c.val.val=c.val.val*q.val.val := congrArg Subtype.val he
    change c.val.val*q.val.val*c.val.val⁻¹=q.val.val
    rw [←he',mul_inv_cancel_right]
  exact ⟨c.val,mem_map_of_mem (centralizer z).subtype hcZ,hf⟩


end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
