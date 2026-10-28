module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAlignedSplit

/-!
# Nonquadratic cubic action from the original aligned cores

The two original order243 cores have disjoint derived lines, so their whole
order81 intersection is elementary abelian. If an element r of the opposite
core outside the first core acted quadratically modulo the first derived line,
its double commutators would lie in both derived lines and vanish. The common
core and r generate the opposite core. Hence the first core would act trivially
on the opposite central quotient, contradicting the already proved exact kernel.

This proves nonquadratic action on the literal four-dimensional abelianization.
Its second displacement image is exactly the opposite marked cubic line in
that quotient, and its third displacement is zero. An actual such actor is
constructed inside the aligned opposite core. These facts constrain the missing
full GL₂(3) action comparison, without assuming a representation equivalence.
The literal source application is Chapter14CoreNonquadratic.

Source: Aschbacher–Smith I.4(G1)–(G2) and I.4.5, printed p.417, using the
original marked cubic normalizers and their Sylow alignment. Compatible Atlas
endpoint maps and the independent strongly-three-embedded exclusion remain open.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace AlignedCubicPair
variable {t : CubicTorus c} (p : AlignedCubicPair t)

private theorem core_pair :
    p.leftCore ⊔ p.rightCore=t.leftCoreExtension ∧
      Nat.card (p.leftCore⊓p.rightCore:Subgroup G)=81 ∧
      ⁅p.rightCore,p.rightCore⁆=(zpowers ((t.y:c.H):G)).map
        (MulAut.conj p.aligner).toMonoidHom :=
  t.maximal_aligned_core_pair p.core_order p.aligner p.aligned

omit [Finite G] in
private theorem left_core_le_middle : p.leftCore≤t.leftCubicBorel :=
  le_sup_left.trans le_sup_left

private theorem right_core_le_middle : p.rightCore≤t.leftCubicBorel := by
  rw [←t.maximal_aligned_borels p.core_order p.aligner p.aligned]
  exact map_mono (le_sup_left.trans le_sup_left)

private theorem cores_normalize :
    p.rightCore≤normalizer (p.leftCore:Set G) ∧
      p.leftCore≤normalizer (p.rightCore:Set G) := by
  constructor
  · exact p.right_core_le_middle.trans (t.leftCubicBorel_le.trans t.cubic_core_normalized)
  · have hn : p.rightEndpoint≤normalizer (p.rightCore:Set G) := by
      rw [rightCore,←map_normalizer_eq_of_bijective _ (MulAut.conj p.aligner).bijective]
      exact map_mono t.swap.cubic_core_normalized
    exact p.left_core_le_middle.trans ((p.overlap ▸ inf_le_right).trans hn)

/-- The two original derived lines are disjoint after the actual Sylow alignment. -/
theorem aligned_derived_disjoint : Disjoint ⁅p.leftCore,p.leftCore⁆ ⁅p.rightCore,p.rightCore⁆ := by
  rw [show ⁅p.leftCore,p.leftCore⁆=zpowers ((t.x:c.H):G) from
    t.maximal_core_derived p.core_order,p.core_pair.2.2]
  let X := zpowers ((t.x:c.H):G)
  let Y := (zpowers ((t.y:c.H):G)).map (MulAut.conj p.aligner).toMonoidHom
  have hx : Nat.card X=3 := by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]
  have hy : Nat.card Y=3 := by
    rw [card_map_of_injective (MulAut.conj p.aligner).injective,
      Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order]
  have hd : Nat.card (X⊓Y:Subgroup G)∣3 := hx ▸ card_dvd_of_le (show X⊓Y≤X from inf_le_left)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact disjoint_iff.mpr (Subgroup.card_eq_one.mp h)
  · have heX : X⊓Y=X := eq_of_le_of_card_ge inf_le_left (by rw [hx,h])
    have heY : X⊓Y=Y := eq_of_le_of_card_ge inf_le_right (by rw [hy,h])
    exact (cubic_lines_not_conjugate (swapFactors c) t.y t.x t.y_order p.aligner
      (heY.symm.trans heX)).elim

/-- The whole common core is elementary abelian of order81. -/
theorem aligned_common_core_elementary : IsElementaryAbelian 3
    (p.leftCore⊓p.rightCore:Subgroup G) := by
  have hcomm : ⁅p.leftCore⊓p.rightCore,p.leftCore⊓p.rightCore⁆=⊥ :=
    eq_bot_iff.mpr ((le_inf (commutator_mono inf_le_left inf_le_left)
      (commutator_mono inf_le_right inf_le_right)).trans p.aligned_derived_disjoint.le_bot)
  let : IsMulCommutative (p.leftCore⊓p.rightCore:Subgroup G) :=
    commutator_self_eq_bot_iff.mp hcomm
  refine {exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_}
  intro a
  apply Subtype.ext
  exact congrArg (fun x : cubicOddCore c t.x => (x:G)) (t.left_oddCore_cube ⟨a,a.property.1⟩)

/-- The first derived line lies in the center of the opposite aligned core. -/
theorem aligned_left_derived_le_right_center : ⁅p.leftCore,p.leftCore⁆≤centerIn p.rightCore := by
  have hZ : centerIn t.leftCoreExtension≤centerIn p.rightCore := by
    rw [←p.aligned,rightCore,←centerIn_map_equiv,←centerIn_map_equiv]
    exact map_mono ((t.swap.maximal_extension_center p.right_core_order).le.trans inf_le_left)
  apply le_trans ?_ hZ
  rw [t.maximal_core_derived p.core_order,
    ←t.maximal_aligned_center_lines p.core_order p.aligner p.aligned]
  exact le_sup_left

private theorem right_generated (r : G) (hr : r∈p.rightCore) (hrD : r∉p.leftCore) :
    (p.leftCore⊓p.rightCore)⊔zpowers r=p.rightCore := by
  let K := p.leftCore⊓p.rightCore
  let J := K⊔zpowers r
  have hJR : J≤p.rightCore := sup_le inf_le_right (zpowers_le.mpr hr)
  have hR : Nat.card p.rightCore=243 := by
    rw [rightCore,card_map_of_injective (MulAut.conj p.aligner).injective,p.right_core_order]
  have hd : Nat.card J∣3^5 := by
    have h := card_dvd_of_le hJR
    rwa [hR] at h
  have hlo : 81≤Nat.card J := p.core_pair.2.1 ▸ card_le_of_le (show K≤J from le_sup_left)
  have hne : Nat.card J≠81 := by
    intro he
    have hKJ : K=J := eq_of_le_of_card_ge le_sup_left (by rw [he,p.core_pair.2.1])
    have hrK : r∈K := hKJ.symm ▸ (show r∈J from mem_sup_right (mem_zpowers _))
    exact hrD hrK.1
  obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=5)).mp hd
  have hn4 : 4≤n := (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp (he ▸ hlo)
  have hn5 : n=5 := by
    by_contra h
    have hn' : n=4 := by omega
    exact hne (by simpa only [hn',Nat.reducePow] using he)
  exact eq_of_le_of_card_ge hJR (by rw [hR,he,hn5]; decide)

private theorem commutator_mem_common (r d : G) (hr : r∈p.rightCore) (hd : d∈p.leftCore) :
    ⁅r,d⁆∈p.leftCore⊓p.rightCore := by
  exact ⟨(le_normalizer_iff_commutator_le_right.mp p.cores_normalize.1)
    (commutator_mem_commutator hr hd),
    (le_normalizer_iff_commutator_le_left.mp p.cores_normalize.2)
      (commutator_mem_commutator hr hd)⟩

private theorem quadratic_commutator_central (r : G) (hr : r∈p.rightCore)
    (hrD : r∉p.leftCore)
    (hq : ∀ d∈p.leftCore,⁅r,⁅r,d⁆⁆∈⁅p.leftCore,p.leftCore⁆)
    (d : G) (hd : d∈p.leftCore) : ⁅r,d⁆∈centerIn p.rightCore := by
  have hk := p.commutator_mem_common r d hr hd
  have hdouble : ⁅r,⁅r,d⁆⁆=1 := p.aligned_derived_disjoint.le_bot
    ⟨hq d hd,commutator_mem_commutator hr hk.2⟩
  have hrcomm : r*⁅r,d⁆=⁅r,d⁆*r := commutatorElement_eq_one_iff_mul_comm.mp hdouble
  refine ⟨hk.2,?_⟩
  have hcentral : p.rightCore≤centralizer ({⁅r,d⁆}:Set G) := by
    rw [←p.right_generated r hr hrD]
    apply sup_le
    · intro k hk'
      let := p.aligned_common_core_elementary
      exact mem_centralizer_singleton_iff.mpr
        (congrArg (fun a : (p.leftCore⊓p.rightCore:Subgroup G) => (a:G))
          (mul_comm (⟨k,hk'⟩:(p.leftCore⊓p.rightCore:Subgroup G)) ⟨⁅r,d⁆,hk⟩))
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hrcomm)
  intro v hv
  exact mem_centralizer_singleton_iff.mp (hcentral hv)


omit [Finite G] in
private theorem central_quotient_conj_iff (R : Subgroup G) (a : normalizer (R:Set G)) (v : R) :
    QuotientGroup.mk' (center R) (R.normalizerMonoidHom a v)=
      QuotientGroup.mk' (center R) v ↔ ⁅(a:G),(v:G)⁆∈centerIn R := by
  rw [←mul_inv_eq_one,←map_inv,←map_mul,←MonoidHom.mem_ker,QuotientGroup.ker_mk']
  change R.normalizerMonoidHom a v*v⁻¹∈center R ↔ ⁅(a:G),(v:G)⁆∈centerIn R
  have hm : ⁅(a:G),(v:G)⁆∈R := R.mul_mem
    ((mem_normalizer_iff.mp a.property _).mp v.property) (R.inv_mem v.property)
  constructor
  · intro h
    refine ⟨hm,?_⟩
    intro w hw
    exact congrArg Subtype.val (mem_center_iff.mp h ⟨w,hw⟩)
  · intro h
    apply mem_center_iff.mpr
    intro w
    exact Subtype.ext (h.2 w w.property)

private theorem quadratic_central_action (r : G) (hr : r∈p.rightCore)
    (hrD : r∉p.leftCore)
    (hq : ∀ d∈p.leftCore,⁅r,⁅r,d⁆⁆∈⁅p.leftCore,p.leftCore⁆)
    (d : G) (hd : d∈p.leftCore) :
    ∀ v∈p.rightCore,⁅d,v⁆∈centerIn p.rightCore := by
  let a : normalizer (p.rightCore:Set G) := ⟨d,p.cores_normalize.2 hd⟩
  let q := QuotientGroup.mk' (center p.rightCore)
  let E := ((q.comp (p.rightCore.normalizerMonoidHom a).toMonoidHom).eqLocus q).map
    p.rightCore.subtype
  have hmem (v : G) (hv : v∈p.rightCore) : v∈E ↔ ⁅d,v⁆∈centerIn p.rightCore := by
    rw [←central_quotient_conj_iff p.rightCore a ⟨v,hv⟩]
    constructor
    · rintro ⟨w,hw,he⟩
      have hwv : w=(⟨v,hv⟩:p.rightCore) := Subtype.ext he
      exact hwv ▸ hw
    · intro h
      exact ⟨⟨v,hv⟩,h,rfl⟩
  have hRE : p.rightCore≤E := by
    rw [←p.right_generated r hr hrD]
    apply sup_le
    · intro k hk
      apply (hmem k hk.2).mpr
      exact p.aligned_left_derived_le_right_center (commutator_mem_commutator hd hk.1)
    · apply zpowers_le.mpr
      apply (hmem r hr).mpr
      rw [←commutatorElement_inv]
      exact (centerIn p.rightCore).inv_mem (p.quadratic_commutator_central r hr hrD hq d hd)
  intro v hv
  exact (hmem v hv).mp (hRE hv)

/-- Trivial action on the literal opposite central quotient detects the opposite core. -/
theorem right_core_of_central_commutators (a : p.rightEndpoint)
    (ha : ∀ v∈p.rightCore,⁅(a:G),v⁆∈centerIn p.rightCore) : (a:G)∈p.rightCore := by
  let b := p.rightEndpointEquiv.symm a
  have hN := t.swap.cubic_core_normalized b.property
  have hcentral (v : cubicOddCore (swapFactors c) t.swap.x) :
      ⁅(b:G),(v:G)⁆∈centerIn (cubicOddCore (swapFactors c) t.swap.x) := by
    have hh := ha (MulAut.conj p.aligner (v:G))
      (mem_map_of_mem (MulAut.conj p.aligner).toMonoidHom v.property)
    have hab : (a:G)=MulAut.conj p.aligner (b:G) :=
      congrArg Subtype.val (p.rightEndpointEquiv.apply_symm_apply a).symm
    rw [hab,←map_commutatorElement] at hh
    rw [rightCore,←centerIn_map_equiv] at hh
    exact (mem_map_iff_mem (MulAut.conj p.aligner).injective).mp hh
  have hk : b∈t.swap.cubicCentralQuotientAction.ker := by
    apply MulEquiv.ext
    intro v
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective
      (center (cubicOddCore (swapFactors c) t.swap.x)) v
    change quotientAut _ ((cubicOddCore (swapFactors c) t.swap.x).normalizerMonoidHom
      ⟨b,hN⟩) (QuotientGroup.mk' _ v)=QuotientGroup.mk' _ v
    rw [quotientAut_apply_mk]
    exact (central_quotient_conj_iff (cubicOddCore (swapFactors c) t.swap.x)
      ⟨(b:G),hN⟩ v).mpr (hcentral v)
  rw [t.swap.cubicCentralQuotientAction_kernel p.right_core_order] at hk
  have hh := mem_map_of_mem (MulAut.conj p.aligner).toMonoidHom
    (show (b:G)∈cubicOddCore (swapFactors c) t.swap.x from hk)
  have hab : MulAut.conj p.aligner (b:G)=(a:G) :=
    congrArg Subtype.val (p.rightEndpointEquiv.apply_symm_apply a)
  exact hab ▸ hh

/-- The opposite original cubic cannot act quadratically modulo the left derived line. -/
theorem aligned_not_quadratic (r : G) (hr : r∈p.rightCore) (hrD : r∉p.leftCore) :
    ∃ d∈p.leftCore,⁅r,⁅r,d⁆⁆∉⁅p.leftCore,p.leftCore⁆ := by
  by_contra hn
  push Not at hn
  have hDR : p.leftCore≤p.rightCore := by
    intro d hd
    apply p.right_core_of_central_commutators
      ⟨d,(p.overlap ▸ inf_le_right) (p.left_core_le_middle hd)⟩
    exact p.quadratic_central_action r hr hrD hn d hd
  have hh := p.core_pair.2.1
  rw [inf_eq_left.mpr hDR,p.core_order] at hh
  omega


/-- Conjugation by the actual opposite-core element on the full left abelianization. -/
def oppositeDisplacement (r : p.rightCore) :
    (p.leftCore ⧸ cubicCoreLine c t.x) →* (p.leftCore ⧸ cubicCoreLine c t.x) := by
  let := t.left_oddCore_quotient_elementary
  let a : cubicNormalizer c t.x := ⟨r,by exact t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩
  exact {
    toFun v := t.cubicAbelianizationAction a v*v⁻¹
    map_one' := by simp
    map_mul' v w := by simp only [map_mul,mul_inv_rev]; ac_rfl }

private def oppositeCoreAutomorphism (r : p.rightCore) : MulAut p.leftCore :=
  t.cubicCoreAction ⟨r,by exact t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩

private theorem oppositeDisplacement_mk (r : p.rightCore) (v : p.leftCore) :
    p.oppositeDisplacement r (QuotientGroup.mk' (cubicCoreLine c t.x) v)=
      QuotientGroup.mk' (cubicCoreLine c t.x) (p.oppositeCoreAutomorphism r v*v⁻¹) := by
  change t.cubicAbelianizationAction _ _*_=_
  rw [t.cubicAbelianizationAction_mk,map_mul,map_inv]
  rfl

/-- The second displacement in the literal quotient is nonzero. -/
theorem oppositeDisplacement_square_ne_one (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    (p.oppositeDisplacement r).comp (p.oppositeDisplacement r)≠1 := by
  obtain ⟨d,hd,hnd⟩ := p.aligned_not_quadratic r r.property hr
  intro he
  let v : p.leftCore := ⟨d,hd⟩
  have hh := DFunLike.congr_fun he (QuotientGroup.mk' (cubicCoreLine c t.x) v)
  change p.oppositeDisplacement r (p.oppositeDisplacement r
    (QuotientGroup.mk' (cubicCoreLine c t.x) v))=1 at hh
  rw [p.oppositeDisplacement_mk,p.oppositeDisplacement_mk] at hh
  have hm := (QuotientGroup.eq_one_iff (p.oppositeCoreAutomorphism r
    (p.oppositeCoreAutomorphism r v*v⁻¹)*(p.oppositeCoreAutomorphism r v*v⁻¹)⁻¹)).mp hh
  apply hnd
  rw [t.maximal_core_derived p.core_order]
  exact hm

/-- The square image is contained in the literal opposite derived line in the left quotient. -/
theorem oppositeDisplacement_square_range_le (r : p.rightCore) :
    ((p.oppositeDisplacement r).comp (p.oppositeDisplacement r)).range ≤
      (⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) := by
  rintro v ⟨w,rfl⟩
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) w
  change p.oppositeDisplacement r (p.oppositeDisplacement r
    (QuotientGroup.mk' (cubicCoreLine c t.x) w))∈_
  rw [p.oppositeDisplacement_mk,p.oppositeDisplacement_mk]
  apply mem_map_of_mem
  change ⁅(r:G),⁅(r:G),(w:G)⁆⁆∈⁅p.rightCore,p.rightCore⁆
  exact commutator_mem_commutator r.property (p.commutator_mem_common r w r.property w.property).2

/-- The opposite displacement has nilpotence length at most three. -/
theorem oppositeDisplacement_cube (r : p.rightCore)
    (v : p.leftCore ⧸ cubicCoreLine c t.x) :
    p.oppositeDisplacement r (p.oppositeDisplacement r (p.oppositeDisplacement r v))=1 := by
  let := t.left_oddCore_quotient_elementary
  let a : cubicNormalizer c t.x := ⟨r,by exact t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩
  let b := t.cubicAbelianizationAction a
  have hr : (r:G)^3=1 := by
    obtain ⟨w,hw,he⟩ := r.property
    rw [←he,←map_pow]
    have hh := congrArg Subtype.val (t.swap.left_oddCore_cube ⟨w,hw⟩)
    change w^3=1 at hh
    rw [hh,map_one]
  have ha : a^3=1 := Subtype.ext hr
  have hb : b^3=1 := by rw [←map_pow,ha,map_one]
  have hb3 (x) : b (b (b x))=x := DFunLike.congr_fun hb x
  have hf (x) : p.oppositeDisplacement r x=b x*x⁻¹ := rfl
  have h3 (x : p.leftCore ⧸ cubicCoreLine c t.x) : x^3=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 _) x
  have hsq (x : p.leftCore ⧸ cubicCoreLine c t.x) : x⁻¹*x⁻¹=x := by
    apply inv_injective
    simp only [mul_inv_rev,inv_inv]
    apply mul_eq_one_iff_eq_inv.mp
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using h3 x
  have hff (x) : p.oppositeDisplacement r (p.oppositeDisplacement r x)=b (b x)*b x*x := by
    simp only [hf,map_mul,map_inv,mul_inv_rev,inv_inv]
    calc
      _ = b (b x)*((b x)⁻¹*(b x)⁻¹)*x := by ac_rfl
      _ = _ := by rw [hsq]
  rw [hf,hff,map_mul,map_mul,hb3]
  have he : v*b (b v)*b v=b (b v)*b v*v := by ac_rfl
  rw [he,mul_inv_cancel]

/-- The actual second displacement recovers the opposite marked line, not an arbitrary line. -/
theorem oppositeDisplacement_square_range (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ((p.oppositeDisplacement r).comp (p.oppositeDisplacement r)).range =
      (⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) := by
  let f := (p.oppositeDisplacement r).comp (p.oppositeDisplacement r)
  let Y := (⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
    (QuotientGroup.mk' (cubicCoreLine c t.x))
  have hY : Nat.card Y∣3 := by
    have h1 := card_map_dvd (⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore)
      (QuotientGroup.mk' (cubicCoreLine c t.x))
    have h2 : Nat.card (⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore)∣3 := by
      have hc : Nat.card (⁅p.rightCore,p.rightCore⁆:Subgroup G)=3 := by
        rw [p.core_pair.2.2,card_map_of_injective (MulAut.conj p.aligner).injective,
          Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order]
      let j : (⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore) →* (⁅p.rightCore,p.rightCore⁆:Subgroup G) :=
        { toFun x := ⟨x,x.property⟩, map_one' := rfl, map_mul' _ _ := rfl }
      have hj : Function.Injective j := by
        intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : (⁅p.rightCore,p.rightCore⁆:Subgroup G) => (z:G)) h
      exact hc ▸ card_dvd_of_injective j hj
    exact h1.trans h2
  have hle := p.oppositeDisplacement_square_range_le r
  have hne : f.range≠⊥ := by
    intro h
    apply p.oppositeDisplacement_square_ne_one r hr
    apply MonoidHom.ext
    intro v
    change f v=1
    exact (show f v∈(⊥:Subgroup _) from h ▸ (show f v∈f.range from ⟨v,rfl⟩))
  have hlo : 3≤Nat.card f.range := by
    have hd := (card_dvd_of_le hle).trans hY
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact (hne (Subgroup.card_eq_one.mp h)).elim
    · exact h.ge
  exact eq_of_le_of_card_ge hle ((Nat.le_of_dvd (by decide) hY).trans hlo)


/-- A nonquadratic cubic actor is constructed inside the actual opposite aligned core. -/
theorem exists_oppositeDisplacement_nonquadratic :
    ∃ r : p.rightCore, (r:G)∉p.leftCore ∧
      (p.oppositeDisplacement r).comp (p.oppositeDisplacement r)≠1 := by
  have hnot : ¬p.rightCore≤p.leftCore := by
    intro h
    have hh := p.core_pair.2.1
    rw [inf_eq_right.mpr h,rightCore,
      card_map_of_injective (MulAut.conj p.aligner).injective,p.right_core_order] at hh
    omega
  obtain ⟨r,hr,hrD⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨⟨r,hr⟩,hrD,p.oppositeDisplacement_square_ne_one ⟨r,hr⟩ hrD⟩

end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
