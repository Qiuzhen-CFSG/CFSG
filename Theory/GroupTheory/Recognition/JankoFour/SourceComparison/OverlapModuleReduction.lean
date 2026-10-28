module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCentralKernel
public import Theory.Mathieu.M22.CentralCover.HexadPerfect
public import Theory.GroupTheory.CyclicThreeNormalizer

/-!
# Reduction of every original overlap automorphism to the section commutant

The even hexad preimage in the original triple cover has index 77.
Transfer retains its cubic kernel in the commutator subgroup, making the
preimage perfect. An automorphism of the full cubic hexad extension which
is trivial modulo the cubic is therefore scalar-inner. Combined with the
already constructed Todd factorization, this reduces every automorphism
of I to the kernel on the full I/Q, retaining the original cubic.

Sylow conjugacy supplies a further correction through Q alone. The residual
fixes the specified cubic pointwise, and its induced action on Q/Z(Q)
commutes with every original overlap actor. If that section action is
trivial, cubic fixed-point freeness removes the inner-Q ambiguity and the
residual is precisely identity or the original plane central twist.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
The remaining module calculation must prove this residual section action
trivial. No commutant classification or compatible local maps are assumed.
Overlap agreement, the full edge equation, and recognition remain separate.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu
open scoped Pointwise

private theorem cubic_outer_inverts {J : Type*} [Group J] [Finite J]
    (A : Subgroup J) [A.Normal] (hc : Nat.card A = 3)
    (t : J) (ht : t ∉ Subgroup.centralizer (A : Set J))
    (x : J) (hx : x ∈ A) : t*x*t⁻¹=x⁻¹ := by
  by_cases hn : x=1
  · simp [hn]
  rcases cyclicThree_normalizer_conjugates A hc x hx hn t
    (by rw [A.normalizer_eq_top]; exact mem_top _) with he | he
  · exfalso
    apply ht
    have hgen := (cyclicThree_generator A hc x hx hn).1
    intro y hy
    change y ∈ A at hy
    rw [←hgen,mem_zpowers_iff] at hy
    obtain ⟨n,rfl⟩ := hy
    have htx : Commute t x := (mul_inv_eq_iff_eq_mul.mp he)
    exact (htx.zpow_right n).eq.symm
  · exact he

/-- A cubic extension with perfect centralizer of index two has no
additional automorphisms over its quotient: all are scalar conjugations. -/
theorem cubic_extension_automorphism_kernel
    {J B : Type*} [Group J] [Finite J] [Group B]
    (p : J →* B) (K : Subgroup J) (hK : K = Subgroup.centralizer (p.ker : Set J))
    (hi : K.index=2) (hAK : p.ker ≤ K) [Group.IsPerfect K]
    (hc : Nat.card p.ker=3) (f : MulAut J) (hf : ∀ x, p (f x)=p x) :
    ∃ c : p.ker, f = MulAut.conj c.val := by
  have hmem (x : J) : f x*x⁻¹ ∈ p.ker := by
    change p (f x*x⁻¹)=1
    rw [map_mul,map_inv,hf,mul_inv_cancel]
  have hfix (x : K) : f x.val=x.val := by
    let r : K →* K := (f.toMonoidHom.comp K.subtype).codRestrict K (fun x => by
      have hh := K.mul_mem (hAK (hmem x)) x.property
      change f x.val ∈ K
      simpa only [inv_mul_cancel_right] using hh)
    have hk : (p.comp K.subtype).ker ≤ center K := by
      intro x hx
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hy := hK.le y.property
      exact (hy x.val hx).symm
    have hr : r = MonoidHom.id K := by
      apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
        (p.comp K.subtype) hk
      exact MonoidHom.ext (fun x => hf x.val)
    exact congrArg Subtype.val (DFunLike.congr_fun hr x)
  have hne : K ≠ ⊤ := by intro he; rw [he,index_top] at hi; contradiction
  obtain ⟨t,ht⟩ : ∃ t : J, t ∉ K := by
    by_contra hn
    exact hne (eq_top_iff.mpr (fun x _ => by simpa using not_exists.mp hn x))
  let d : p.ker := ⟨f t*t⁻¹,hmem t⟩
  let c := d⁻¹
  have hct : c.val*t*c.val⁻¹=f t := by
    have hinv := cubic_outer_inverts p.ker hc t (by rwa [←hK]) c.val⁻¹
      (p.ker.inv_mem c.property)
    have hcc : c.val*c.val=d.val := by
      change d.val⁻¹*d.val⁻¹=d.val
      have hd3 : d.val^3=1 := by
        have he : d^Nat.card p.ker=1 := pow_card_eq_one'
        rw [hc] at he
        exact congrArg Subtype.val he
      calc
        _ = (d.val*d.val)⁻¹ := (mul_inv_rev _ _).symm
        _ = (d.val⁻¹)⁻¹ := by congr 1; apply mul_eq_one_iff_eq_inv.mp; simpa [pow_succ] using hd3
        _ = d.val := inv_inv _
    calc
      _ = c.val*(t*c.val⁻¹*t⁻¹)*t := by group
      _ = c.val*c.val*t := by rw [hinv,inv_inv,mul_assoc]
      _ = d.val*t := by rw [hcc]
      _ = f t := by dsimp [d]; group
  refine ⟨c,MulEquiv.ext (fun x => ?_)⟩
  by_cases hx : x ∈ K
  · have hcx : x*c.val=c.val*x := (hK.le hx c.val c.property).symm
    rw [hfix ⟨x,hx⟩,MulAut.conj_apply,←hcx,mul_inv_cancel_right]
  · have hy : x*t⁻¹ ∈ K := (mul_mem_iff_of_index_two hi).mpr
      (iff_of_false hx (fun hh => ht (K.inv_mem_iff.mp hh)))
    have hcy : (x*t⁻¹)*c.val=c.val*(x*t⁻¹) := (hK.le hy c.val c.property).symm
    have he := hfix ⟨x*t⁻¹,hy⟩
    rw [map_mul,map_inv] at he
    have hex : f x=(x*t⁻¹)*f t := mul_inv_eq_iff_eq_mul.mp he
    rw [hex,←hct,MulAut.conj_apply]
    calc
      _ = ((x*t⁻¹)*c.val)*t*c.val⁻¹ := by group
      _ = (c.val*(x*t⁻¹))*t*c.val⁻¹ := by rw [hcy]
      _ = _ := by group

/-- Sylow conjugacy can be corrected through the normal supplement alone.
The correction preserves the same specified Sylow subgroup. -/
theorem automorphism_sylow_correction
    {J : Type*} [Group J] [Finite J] {p : ℕ} [Fact p.Prime]
    (Q R : Subgroup J) [Q.Normal] [R.Characteristic] (P : Sylow p R)
    (hgen : Q ⊔ (P : Subgroup R).map R.subtype = R) (f : MulAut J) :
    ∃ (q : Q) (b : MulAut J),
      ((P : Subgroup R).map R.subtype).map b.toMonoidHom = (P : Subgroup R).map R.subtype ∧
      f=MulAut.conj q.val*b := by
  let A := (P : Subgroup R).map R.subtype
  let F := MulAut.characteristic R f
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq R (F • P) P
  have he := congrArg (fun U : Sylow p R => (U : Subgroup R)) hk
  rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def,
    Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def] at he
  have hh := congrArg (Subgroup.map R.subtype) he
  have hmap : A.map ((MulAut.conj k.val)*f).toMonoidHom=A := by
    dsimp only [A]
    rw [map_map]
    change (((P : Subgroup R).map F.toMonoidHom).map
      (MulAut.conj k).toMonoidHom).map R.subtype = _ at hh
    rw [map_map,map_map] at hh
    exact hh
  have hm : k.val ∈ A ⊔ Q := by rw [sup_comm,hgen]; exact k.property
  obtain ⟨s,hs,q,hq,hkq⟩ := mem_sup_of_normal_right.mp hm
  let b := MulAut.conj q*f
  have hsA : A.map (MulAut.conj s).toMonoidHom=A :=
    mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer hs)
  have hb : A.map b.toMonoidHom=A := by
    apply Subgroup.map_injective (f := (MulAut.conj s).toMonoidHom) (MulAut.conj s).injective
    rw [hsA,map_map]
    have hc : (MulAut.conj k.val*f).toMonoidHom =
        (MulAut.conj s).toMonoidHom.comp b.toMonoidHom := by
      rw [←hkq,map_mul]
      rfl
    rwa [hc] at hmap
  refine ⟨⟨q⁻¹,Q.inv_mem hq⟩,b,hb,?_⟩
  change f=MulAut.conj q⁻¹*(MulAut.conj q*f)
  rw [map_inv,inv_mul_cancel_left]

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

/-- The actual hexad preimage in the perfect triple cover in H/Q. -/
noncomputable def overlapEvenCover : Subgroup (innerPreimage a.e) :=
  (MulAction.stabilizer M22 a.P.hexad).comap (innerProjection a.e)

theorem overlapEvenCover_perfect : Group.IsPerfect (overlapEvenCover a) := by
  let : Group.IsPerfect (innerPreimage a.e) := ⟨innerPreimage_derived_eq_top h a.e⟩
  let L := overlapEvenCover a
  let p := innerProjection a.e
  let H := MulAction.stabilizer M22 a.P.hexad
  let : Group.IsPerfect H := m22HexadStabilizer_isPerfect a.P.hexad_mem
  have hk : p.ker ≤ L := by intro x hx; change p x ∈ H; rw [hx]; exact H.one_mem
  have hi : L.index=77 := by
    change (H.comap p).index=77
    rw [index_comap_of_surjective _ (innerProjection_surjective a.e)]
    have hc := H.card_mul_index
    rw [m22Hexad_stabilizer_card a.P.hexad_mem,m22_order] at hc
    omega
  have hz : p.ker ≤ ⁅L,L⁆ := central_pSubgroup_le_commutator L p.ker hk
    (innerProjection_kernel_central a.e)
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using innerProjection_kernel_card a.e))
    (by rw [hi]; decide)
  let q := p.subgroupComap H
  have hq : Function.Surjective q := p.subgroupComap_surjective_of_surjective H
    (innerProjection_surjective a.e)
  have hqk : q.ker ≤ commutator L := by
    intro x hx
    have hx' : x.val ∈ p.ker := congrArg Subtype.val hx
    have hm := hz hx'
    rw [←map_subtype_commutator] at hm
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y=x) ▸ hy
  exact ⟨(sup_of_le_right hqk).symm.trans
    (CentralExtension.ker_sup_commutator_eq_top_of_surjective q hq)⟩

private theorem conj_mem_designStabilizer_iff (B : Finset (Fin 22)) (x : M22) :
    MulAut.conj x ∈ designStabilizer B ↔ x ∈ MulAction.stabilizer M22 B := by
  let g := M22ValueBound.Concrete.inclusion x
  have hg : m22DesignAutToAut g = MulAut.conj x :=
    M22ValueBound.Concrete.designAutEquiv_inclusion x
  constructor
  · rintro ⟨y,hy,he⟩
    have hy' : y=g := m22DesignAutToAut_injective (he.trans hg.symm)
    rw [hy'] at hy
    exact hy
  · intro hx
    exact ⟨g,hx,hg⟩

/-- The image of the literal overlap under H → H/Q, retaining its cubic kernel. -/
noncomputable def overlapCoreImage : Subgroup (centralizer z ⧸ core z) :=
  (designStabilizer a.P.hexad).comap a.e.projection

noncomputable def overlapCoreProjection : PlaneOverlap a →* overlapCoreImage a where
  toFun x := ⟨QuotientGroup.mk' (core z) x.val,by
    have hx := a.P.overlap.le x.property
    rw [a.cubic_eq] at hx
    exact hx⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem overlapCoreProjection_surjective : Function.Surjective (overlapCoreProjection a) := by
  intro x
  obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (core z) x.val
  have hI : y ∈ PlaneOverlap a := by
    rw [show PlaneOverlap a = (designStabilizer a.P.hexad).comap (CubicLift.projection a.e) from
      a.cubic_eq ▸ a.P.overlap]
    change a.e.projection (QuotientGroup.mk' (core z) y) ∈ designStabilizer a.P.hexad
    rw [hy]
    exact x.property
  exact ⟨⟨y,hI⟩,Subtype.ext hy⟩

theorem overlapCoreProjection_ker : (overlapCoreProjection a).ker =
    (core z).subgroupOf (PlaneOverlap a) := by
  ext x
  change (⟨QuotientGroup.mk' (core z) x.val,_⟩ : overlapCoreImage a) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff x.val

noncomputable def overlapCoreScalar : Subgroup (overlapCoreImage a) :=
  a.e.projection.ker.subgroupOf (overlapCoreImage a)

noncomputable def overlapCoreEven : Subgroup (overlapCoreImage a) :=
  (innerPreimage a.e).subgroupOf (overlapCoreImage a)

noncomputable def overlapEvenCoverEquiv : overlapEvenCover a ≃* overlapCoreEven a where
  toFun x := ⟨⟨x.val.val,by
    change a.e.projection x.val.val ∈ designStabilizer a.P.hexad
    rw [←innerProjection_conj a.e x.val]
    exact (conj_mem_designStabilizer_iff _ _).mpr x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,by
    apply (conj_mem_designStabilizer_iff _ _).mp
    rw [innerProjection_conj]
    exact x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem overlapCoreEven_perfect : Group.IsPerfect (overlapCoreEven a) := by
  let := overlapEvenCover_perfect a
  exact Group.IsPerfect.ofSurjective (f := (overlapEvenCoverEquiv a).toMonoidHom)
    (overlapEvenCoverEquiv a).surjective

theorem overlapCoreScalar_card : Nat.card (overlapCoreScalar a)=3 := by
  unfold overlapCoreScalar
  rw [Nat.card_congr (subgroupOfEquivOfLe (show a.e.projection.ker ≤ overlapCoreImage a from
    fun x hx => by change a.e.projection x ∈ designStabilizer a.P.hexad; rw [hx]; exact one_mem _)).toEquiv]
  exact a.e.kernel_card

theorem overlapCoreScalar_le_even : overlapCoreScalar a ≤ overlapCoreEven a := by
  intro x hx
  change a.e.projection x.val ∈ MulAut.innerSubgroup M22
  rw [show a.e.projection x.val=1 from hx]
  exact one_mem _

theorem overlapCoreScalar_centralizer :
    Subgroup.centralizer (overlapCoreScalar a : Set (overlapCoreImage a)) = overlapCoreEven a := by
  ext x
  constructor
  · intro hx
    change x.val ∈ innerPreimage a.e
    rw [←centralizer_cubicKernel h a.e]
    intro c hc
    let c' : overlapCoreImage a := ⟨c,by change a.e.projection c ∈ designStabilizer a.P.hexad; rw [hc]; exact one_mem _⟩
    exact congrArg Subtype.val (hx c' hc)
  · intro hx c hc
    have hh : x.val ∈ Subgroup.centralizer (a.e.projection.ker : Set _) :=
      (centralizer_cubicKernel h a.e).ge hx
    exact Subtype.ext (hh c.val hc)

theorem overlapCoreEven_index : (overlapCoreEven a).index=2 := by
  have hi : (innerPreimage a.e).index=2 := by
    change ((MulAut.innerSubgroup M22).comap a.e.projection).index=2
    rw [index_comap_of_surjective _ a.e.surjective,index_eq_card]
    exact Nat.le_antisymm (Nat.le_of_dvd (by decide)
      M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two) m22Out_card_lower_bound
  have hd : (overlapCoreEven a).index ∣ 2 :=
    hi ▸ relIndex_dvd_index_of_normal (innerPreimage a.e) (overlapCoreImage a)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exfalso
    have hl : overlapCoreImage a ≤ innerPreimage a.e :=
      subgroupOf_eq_top.mp (index_eq_one.mp he)
    have hdesign : designStabilizer a.P.hexad ≤ MulAut.innerSubgroup M22 := by
      intro y hy
      obtain ⟨x,hx⟩ := a.e.surjective y
      have hm : x ∈ overlapCoreImage a := by change a.e.projection x ∈ designStabilizer a.P.hexad; rwa [hx]
      have hh := hl hm
      change a.e.projection x ∈ MulAut.innerSubgroup M22 at hh
      rwa [hx] at hh
    have hc : Nat.card (MulAut.innerSubgroup M22)=443520 :=
      (Nat.card_congr (MonoidHom.ofInjective
        (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).toEquiv).symm.trans m22_order
    have hh := card_dvd_of_le hdesign
    rw [native_design_hex_card a.P.hexad_mem,hc] at hh
    norm_num at hh
  · exact he

noncomputable def overlapCoreQuotientEquiv :
    (PlaneOverlap a ⧸ (core z).subgroupOf (PlaneOverlap a)) ≃* overlapCoreImage a :=
  (QuotientGroup.quotientMulEquivOfEq (overlapCoreProjection_ker a).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (overlapCoreProjection_surjective a))

theorem overlapCoreQuotientEquiv_mk (x : PlaneOverlap a) :
    overlapCoreQuotientEquiv a (QuotientGroup.mk' _ x) = overlapCoreProjection a x := rfl

noncomputable def overlapCoreImageAut (f : MulAut (PlaneOverlap a)) : MulAut (overlapCoreImage a) :=
  MulAut.congr (overlapCoreQuotientEquiv a)
    (QuotientGroup.congr _ _ f (overlap_automorphism_preserves_core a f))

theorem overlapCoreImageAut_projection (f : MulAut (PlaneOverlap a)) (x : PlaneOverlap a) :
    overlapCoreImageAut a f (overlapCoreProjection a x) = overlapCoreProjection a (f x) := by
  rw [←overlapCoreQuotientEquiv_mk]
  change overlapCoreQuotientEquiv a (QuotientGroup.congr _ _ f (overlap_automorphism_preserves_core a f)
    ((overlapCoreQuotientEquiv a).symm (overlapCoreQuotientEquiv a _))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The residual scalar action on I/Q is inner, through the original A.
No action on Q/Z(Q) is assumed. -/
theorem overlap_cubic_quotient_kernel (f : MulAut (PlaneOverlap a))
    (hf : ∀ x : PlaneOverlap a, QuotientGroup.mk'
      ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)) (f x) = QuotientGroup.mk' _ x) :
    ∃ c : PlaneOverlap a, c.val ∈ cubicSylowImage a.e a.X ∧
      ∀ x, overlapCoreProjection a (f x) = overlapCoreProjection a (c*x*c⁻¹) := by
  let p : overlapCoreImage a →* designStabilizer a.P.hexad :=
    a.e.projection.subgroupComap (designStabilizer a.P.hexad)
  have hp : p.ker = overlapCoreScalar a := by
    ext x
    change (⟨a.e.projection x.val,_⟩ : designStabilizer a.P.hexad)=1 ↔ _
    exact Subtype.ext_iff
  let := overlapCoreEven_perfect a
  have hfp : ∀ x, p (overlapCoreImageAut a f x) = p x := by
    intro x
    obtain ⟨y,rfl⟩ := overlapCoreProjection_surjective a x
    rw [overlapCoreImageAut_projection]
    apply Subtype.ext
    have he := congrArg (a.P.planeQuotientEquiv h) (hf y)
    have hh := congrArg Subtype.val he
    change CubicLift.projection a.P.cubic (f y).val = CubicLift.projection a.P.cubic y.val at hh
    rw [a.cubic_eq] at hh
    exact hh
  obtain ⟨c,hc⟩ := cubic_extension_automorphism_kernel p (overlapCoreEven a)
    (by rw [hp,overlapCoreScalar_centralizer]) (overlapCoreEven_index a)
    (hp ▸ overlapCoreScalar_le_even a) (hp ▸ overlapCoreScalar_card a)
    (overlapCoreImageAut a f) hfp
  have hcA : c.val.val ∈ a.e.projection.ker := congrArg Subtype.val c.property
  obtain ⟨d,hd,hdc⟩ := (cubicSylow_map_coreQuotient h a.e a.X).ge hcA
  have hdI : d ∈ PlaneOverlap a := by
    apply overlap_cubicLift_le a
    rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
    exact (le_sup_right : cubicSylowImage a.e a.X ≤ core z ⊔ cubicSylowImage a.e a.X) hd
  let r : PlaneOverlap a := ⟨d,hdI⟩
  have hr : overlapCoreProjection a r = c.val := Subtype.ext hdc
  refine ⟨r,hd,fun x => ?_⟩
  rw [map_mul,map_mul,map_inv,hr,←overlapCoreImageAut_projection,hc]
  rfl

private theorem overlap_quotient_correction (f : MulAut (PlaneOverlap a))
    (hf : ∀ x : PlaneOverlap a, QuotientGroup.mk'
      ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)) (f x) = QuotientGroup.mk' _ x) :
    ∃ (c : PlaneOverlap a) (b : MulAut (PlaneOverlap a)),
      c.val ∈ cubicSylowImage a.e a.X ∧
      (∀ x, overlapCoreProjection a (b x)=overlapCoreProjection a x) ∧
      f=MulAut.conj c*b := by
  obtain ⟨c,hc,he⟩ := overlap_cubic_quotient_kernel a f hf
  let b := (MulAut.conj c)⁻¹*f
  refine ⟨c,b,hc,?_,by dsimp [b]; group⟩
  intro x
  change overlapCoreProjection a ((MulAut.conj c)⁻¹ (f x)) = _
  rw [←map_inv,MulAut.conj_apply,map_mul,map_mul,map_inv,map_inv,he]
  simp only [map_mul,map_inv]
  group

/-- Every automorphism reduces, by constructed inner and Todd corrections,
to the kernel on the full I/Q. The cubic has not been discarded. -/
theorem overlap_automorphism_core_factorization (f : MulAut (PlaneOverlap a)) :
    ∃ (x : PlaneOverlap a) (b : MulAut (PlaneOverlap a)),
      (∀ y, overlapCoreProjection a (b y)=overlapCoreProjection a y) ∧
      (f=MulAut.conj x*b ∨
        f=MulAut.conj x*planeOverlapToddTwist a (cubicFixedWord a)*b) := by
  let π := QuotientGroup.mk' ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a))
  obtain ⟨x,hx⟩ := overlap_automorphism_quotient_factorization a f
  rcases hx with hx | hx
  · let r := (MulAut.conj x)⁻¹*f
    have hr (y) : π (r y)=π y := by
      change π ((MulAut.conj x)⁻¹ (f y))=π y
      rw [←map_inv,MulAut.conj_apply,map_mul,map_mul,map_inv,map_inv,hx]
      simp only [map_mul,map_inv]
      dsimp only [π]
      group
    obtain ⟨c,b,hc,hb,he⟩ := overlap_quotient_correction a r hr
    refine ⟨x*c,b,hb,Or.inl ?_⟩
    have hh : f=MulAut.conj x*r := by dsimp [r]; group
    rw [hh,he,map_mul]
    group
  · let β := planeOverlapToddTwist a (cubicFixedWord a)
    let r := (MulAut.conj x)⁻¹*f*β⁻¹
    have hr (y) : π (r y)=π y := by
      change π ((MulAut.conj x)⁻¹ (f (β⁻¹ y)))=π y
      rw [←map_inv,MulAut.conj_apply,map_mul,map_mul,map_inv,map_inv,hx]
      change π x⁻¹ * (π (x * β (β⁻¹ y) * x⁻¹)) * (π x)⁻¹⁻¹ = π y
      rw [MulAut.apply_inv_self]
      simp only [map_mul,map_inv]
      dsimp only [π]
      group
    obtain ⟨c,b,hc,hb,he⟩ := overlap_quotient_correction a r hr
    let d := β⁻¹*b*β
    have hd (y) : overlapCoreProjection a (d y)=overlapCoreProjection a y := by
      change overlapCoreProjection a (β⁻¹ (b (β y))) = _
      rw [←overlapCoreImageAut_projection,hb,overlapCoreImageAut_projection,
        MulAut.inv_apply_self]
    refine ⟨x*c,d,hd,Or.inr ?_⟩
    have hh : f=MulAut.conj x*r*β := by dsimp [r]; group
    rw [hh,he,map_mul]
    dsimp [d,β]
    group

/-- The actual cubic as a subgroup of I, with its original embedding. -/
noncomputable def overlapCubic : Subgroup (PlaneOverlap a) :=
  (cubicSylowImage a.e a.X).subgroupOf (PlaneOverlap a)

theorem overlapCubic_le_lift : overlapCubic a ≤
    (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) := by
  intro x hx
  change x.val ∈ twoThreeCore (centralizer z)
  rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
  exact (le_sup_right : cubicSylowImage a.e a.X ≤ core z ⊔ cubicSylowImage a.e a.X) hx

theorem overlapCubic_card : Nat.card (overlapCubic a)=3 := by
  have hl : cubicSylowImage a.e a.X ≤ PlaneOverlap a := by
    apply le_trans ?_ (overlap_cubicLift_le a)
    rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
    exact le_sup_right
  exact (Nat.card_congr (subgroupOfEquivOfLe hl).toEquiv).trans
    (cubicSylowImage_card h a.e a.X)

/-- The residual fixing I/Q can be corrected by an element of Q so that
it preserves the literal cubic; it then fixes that cubic pointwise. -/
theorem overlap_core_kernel_cubic_correction (f : MulAut (PlaneOverlap a))
    (hf : ∀ x, overlapCoreProjection a (f x)=overlapCoreProjection a x) :
    ∃ (q : (core z).subgroupOf (PlaneOverlap a)) (b : MulAut (PlaneOverlap a)),
      f=MulAut.conj q.val*b ∧
      (∀ x, overlapCoreProjection a (b x)=overlapCoreProjection a x) ∧
      (overlapCubic a).map b.toMonoidHom=overlapCubic a ∧
      ∀ x : overlapCubic a, b x.val=x.val := by
  let Q := (core z).subgroupOf (PlaneOverlap a)
  let R := (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a)
  let A := overlapCubic a
  have hAR : A ≤ R := overlapCubic_le_lift a
  have hAc : Nat.card (A.subgroupOf R)=3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans (overlapCubic_card a)
  have hRc : Nat.card R=3*2^13 :=
    (Nat.card_congr (subgroupOfEquivOfLe (overlap_cubicLift_le a)).toEquiv).trans (twoThreeCore_card h)
  let P : Sylow 3 R := Sylow.ofCard (A.subgroupOf R) (by
    rw [hAc,hRc,Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,(by decide : Nat.Prime 3).factorization])
  have hP : (P : Subgroup R).map R.subtype=A := map_subgroupOf_eq_of_le hAR
  have hgen : Q ⊔ (P : Subgroup R).map R.subtype=R := by
    rw [hP]
    apply Subgroup.map_injective (PlaneOverlap a).subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le
      ((core_le_twoThreeCore h).trans (overlap_cubicLift_le a)),
      map_subgroupOf_eq_of_le (overlap_cubicLift_le a)]
    change core z ⊔ ((cubicSylowImage a.e a.X).subgroupOf (PlaneOverlap a)).map
      (PlaneOverlap a).subtype = _
    rw [map_subgroupOf_eq_of_le (show cubicSylowImage a.e a.X ≤ PlaneOverlap a from by
      apply le_trans ?_ (overlap_cubicLift_le a)
      rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
      exact le_sup_right),core_sup_cubicSylow a.e h a.X,cubicLift_eq_twoThreeCore h a.e]
  obtain ⟨q,b,hb,he⟩ := automorphism_sylow_correction Q R P hgen f
  rw [hP] at hb
  have hq : overlapCoreProjection a q.val=1 := (overlapCoreProjection_ker a).ge q.property
  have hbf (x) : overlapCoreProjection a (b x)=overlapCoreProjection a x := by
    have hh := hf x
    rw [he,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_mul,map_inv,hq,one_mul,inv_one,mul_one] at hh
    exact hh
  refine ⟨q,b,he,hbf,hb,fun x => ?_⟩
  have haQ : Function.Injective ((overlapCoreProjection a).comp A.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro x hx
    have hQA : Disjoint (core z) (cubicSylowImage a.e a.X) := by
      apply disjoint_of_coprime_natCard
      rw [h.core_card,cubicSylowImage_card h a.e a.X]
      norm_num
    have hxx : x.val.val ∈ core z := (overlapCoreProjection_ker a).le hx
    exact Subtype.ext (Subtype.ext (disjoint_def.mp hQA hxx x.property))
  have hbA : b x.val ∈ A := hb ▸ mem_map_of_mem b.toMonoidHom x.property
  exact congrArg Subtype.val (haQ (show
    ((overlapCoreProjection a).comp A.subtype) ⟨b x.val,hbA⟩ =
      ((overlapCoreProjection a).comp A.subtype) x from hbf x.val))

/-- The action of I on the original extraspecial central quotient. -/
noncomputable def overlapSectionAction : PlaneOverlap a →* MulAut (core z ⧸ center (core z)) :=
  (coreAction z).comp (PlaneOverlap a).subtype

/-- The action induced by an arbitrary automorphism of the original overlap. -/
noncomputable def overlapSectionAut : MulAut (PlaneOverlap a) →* MulAut (core z ⧸ center (core z)) :=
  (quotientAut (center (core z))).comp (overlapCoreAut a)

theorem overlapCoreAut_intertwines (f : MulAut (PlaneOverlap a)) (x : PlaneOverlap a) :
    overlapCoreAut a f * MulAut.conjNormal x.val =
      MulAut.conjNormal (f x).val * overlapCoreAut a f := by
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  change (overlapCoreAut a f (MulAut.conjNormal x.val q)).val =
    (f x).val*(overlapCoreAut a f q).val*(f x).val⁻¹
  rw [overlapCoreAut_coe,overlapCoreAut_coe]
  exact congrArg Subtype.val (f.map_mul (x *
    ⟨q.val,(core_le_twoThreeCore h).trans (overlap_cubicLift_le a) q.property⟩) x⁻¹ |>.trans
      (by rw [map_mul,map_inv]))

theorem overlapSectionAut_intertwines (f : MulAut (PlaneOverlap a)) (x : PlaneOverlap a) :
    overlapSectionAut a f * overlapSectionAction a x =
      overlapSectionAction a (f x) * overlapSectionAut a f := by
  exact (quotientAut (center (core z))).map_mul _ _ |>.symm.trans
    ((congrArg (quotientAut (center (core z))) (overlapCoreAut_intertwines a f x)).trans
      ((quotientAut (center (core z))).map_mul _ _))

/-- Fixing I/Q makes the residual section action commute with all actual
actors, not just the scalar or an independently chosen complement. -/
theorem overlapSectionAut_commutes (f : MulAut (PlaneOverlap a))
    (hf : ∀ x, overlapCoreProjection a (f x)=overlapCoreProjection a x)
    (x : PlaneOverlap a) : Commute (overlapSectionAut a f) (overlapSectionAction a x) := by
  have he : overlapSectionAction a (f x)=overlapSectionAction a x := by
    change coreQuotientAction h (QuotientGroup.mk' (core z) (f x).val) =
      coreQuotientAction h (QuotientGroup.mk' (core z) x.val)
    exact congrArg (coreQuotientAction h) (congrArg Subtype.val (hf x))
  exact (overlapSectionAut_intertwines a f x).trans (congrArg (fun t => t*overlapSectionAut a f) he)

/-- The cubic-fixed section kernel is exactly the plane twist. The inner
core ambiguity is removed by the same fixed-point-free cubic. -/
theorem overlap_cubic_fixed_section_kernel (f : MulAut (PlaneOverlap a))
    (hf : ∀ x : overlapCubic a, f x.val=x.val)
    (hsec : overlapSectionAut a f=1) : f=1 ∨ f=overlapPlaneTwist a := by
  let := h.extraspecial
  have hff (v : core z ⧸ center (core z))
      (hv : ∀ x : a.X, quotientAut (center (core z))
        (MulAut.conjNormal x.val.val) v=v) : v=1 := by
    apply (cubicAction_fixed_iff h a.e a.X v).mp
    intro x
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center (core z)) v
    rw [cubicAction_mk]
    exact (quotientAut_apply_mk _ _ _).symm.trans (hv x)
  have hcomm (x : a.X) : Commute (overlapCoreAut a f) (MulAut.conjNormal x.val.val) := by
    have hx : x.val.val ∈ cubicSylowImage a.e a.X := mem_map_of_mem _ x.property
    have hxI : x.val.val ∈ PlaneOverlap a := by
      apply overlap_cubicLift_le a
      exact (cubicLift_eq_twoThreeCore h a.e).le x.val.property
    have he := overlapCoreAut_intertwines a f ⟨x.val.val,hxI⟩
    rw [hf ⟨⟨x.val.val,hxI⟩,hx⟩] at he
    exact he
  have ha : overlapCoreAut a f=1 := QuadraticLift.quotient_trivial_of_commute_fixedFree
    (fun x : a.X => MulAut.conjNormal x.val.val) hff (overlapCoreAut a f) hsec hcomm
  apply overlap_core_fixer_cases a f
  intro x hx
  apply Subtype.ext
  have he := congrArg (fun q : core z => q.val) (MulEquiv.congr_fun ha ⟨x.val,hx⟩)
  rw [overlapCoreAut_coe] at he
  exact he

/-- An arbitrary original overlap automorphism admits the exact source
reduction: inner and constructed Todd factors, followed by a cubic-fixing
residual whose action commutes with the whole original I/Q action. -/
theorem overlap_automorphism_module_reduction (f : MulAut (PlaneOverlap a)) :
    ∃ (x : PlaneOverlap a) (b : MulAut (PlaneOverlap a)),
      (∀ y, overlapCoreProjection a (b y)=overlapCoreProjection a y) ∧
      (∀ y : overlapCubic a, b y.val=y.val) ∧
      (∀ y, Commute (overlapSectionAut a b) (overlapSectionAction a y)) ∧
      (overlapSectionAut a b=1 → b=1 ∨ b=overlapPlaneTwist a) ∧
      (f=MulAut.conj x*b ∨ f=MulAut.conj x*planeOverlapToddTwist a (cubicFixedWord a)*b) := by
  obtain ⟨x,r,hr,he⟩ := overlap_automorphism_core_factorization a f
  obtain ⟨q,b,hb,hbq,_,hbc⟩ := overlap_core_kernel_cubic_correction a r hr
  have hc := overlapSectionAut_commutes a b hbq
  have hk := overlap_cubic_fixed_section_kernel a b hbc
  rcases he with he | he
  · refine ⟨x*q.val,b,hbq,hbc,hc,hk,Or.inl ?_⟩
    rw [he,hb,map_mul,mul_assoc]
  · let β := planeOverlapToddTwist a (cubicFixedWord a)
    refine ⟨x*β q.val,b,hbq,hbc,hc,hk,Or.inr ?_⟩
    rw [he,hb,map_mul]
    change MulAut.conj x*(β*(MulAut.conj q.val*b)) =
      MulAut.conj x*MulAut.conj (β q.val)*β*b
    have ht : β*MulAut.conj q.val=MulAut.conj (β q.val)*β := by
      apply MulEquiv.ext
      intro y
      simp only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv]
    rw [←mul_assoc β,ht]
    group

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
