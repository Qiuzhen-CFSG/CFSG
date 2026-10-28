module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.SmallCommutatorMiddle
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.DerivedFirst
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Natural

/-!
# The exact derived subgroup of the distance-eight second layer

The second hat has a marked quotient consisting of two dual natural
SL3(2)-modules, and its first hat is central. Its commutator lies in Z.
Modulo the natural subgroup U, conjugation fixes every value of the
commutator pairing. The reciprocal cubic relation of a Singer element
forces that pairing to vanish. Noncommutation on the original critical
window and irreducibility of U then identify the second derived subgroup
with U.

The literal second layer lies in core joined with Z, and Z centralizes
the core. Thus U lies in the core derived subgroup. Combining this with
the proved first-dual occurrence and residual idempotence places the
whole moving radius subgroup Vcirc in the core derived subgroup.

These results use CommonFacts and genuine Earlier only. The opposite
containment and the full component-fixed-factor equality with H remain
separate obligations; neither follows by dropping Z from a quotient.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(v), (4.5.4)(ii)--(iii)
and (4.5.5), printed pp.895,898--900.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open Higher DistanceFour.Linear PathCentrality
open Higher.Quotients.MovingLayer.Singer

private theorem binary_reciprocal_pairing_zero {D E : Type*} [Group D] [CommGroup E]
    (a : MulAut D) (β : D →* (D →* E))
    (hact : ∀ x y, β (a x) (a y) = β x y)
    (hleft : ∀ x, β (a (a (a x)) * a (a x) * x) = 1)
    (hright : ∀ x y, β x (a (a (a y)) * a (a y) * y) = 1)
    (hsquare : ∀ e : E, e * e = 1) : ∀ x y, β x y = 1 := by
  have hstep (x y : D) : β x (a y) = β x (a (a y)) := by
    have hl := congrArg (fun f : D →* E => f (a (a (a y)))) (hleft x)
    simp only [map_mul, MonoidHom.mul_apply, MonoidHom.one_apply] at hl
    rw [hact (a (a x)) (a (a y)),hact (a x) (a y),hact x y,
      hact (a x) (a (a y)),hact x (a y)] at hl
    have hr := hright x y
    simp only [map_mul] at hr
    apply mul_left_cancel (a := β x y * β x (a (a (a y))))
    calc
      _ = β x y * β x (a y) * β x (a (a (a y))) := by ac_rfl
      _ = 1 := hl
      _ = β x (a (a (a y))) * β x (a (a y)) * β x y := hr.symm
      _ = _ := by ac_rfl
  have hfixed (x y : D) : β x (a y) = β x y := by
    simpa only [a.apply_symm_apply] using (hstep x (a.symm y)).symm
  intro x y
  have h := hright x y
  simp only [map_mul,hfixed] at h
  rwa [hsquare,one_mul] at h

private theorem dual_singer_cubic (v : W) :
    dual singer (dual singer (dual singer v)) + dual singer (dual singer v) + v = 0 := by
  have hinv : singer⁻¹ = (⟨!![1,1,0; 0,0,1; 1,0,0], by decide⟩ : S) := by
    apply inv_eq_of_mul_eq_one_right
    decide +kernel
  have h : ∀ v : W,
      dual singer (dual singer (dual singer v)) + dual singer (dual singer v) + v = 0 := by
    simp only [dual,hinv]
    decide +kernel
  exact h v

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

omit [Finite M] in
private theorem marked_dual_pair_derived_le
    (common : CommonFacts R source geometry)
    {B F Z N : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common B F true)
    (hF : F ≤ centralizer (B : Set (FreeAmalgam R)))
    (hBZ : ⁅B,B⁆ ≤ Z) (hZB : Z ≤ centralizer (B : Set (FreeAmalgam R)))
    {E : Type*} [CommGroup E] (q : Z →* E)
    (hker : q.ker = N.subgroupOf Z)
    (hfixed : ∀ (m : M) (x y : Z),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ → q y = q x)
    (hsquare : ∀ e : E, e * e = 1) : ⁅B,B⁆ ≤ N := by
  let row (x : B) : B →* E := {
    toFun y := q ⟨⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆,
      hBZ (commutator_mem_commutator x.property y.property)⟩
    map_one' := by
      change q _ = 1
      rw [show (⟨⁅(x : FreeAmalgam R),((1 : B) : FreeAmalgam R)⁆,_⟩ : Z) = 1 from Subtype.ext (by simp),map_one]
    map_mul' y z := by
      have he : (⟨⁅(x : FreeAmalgam R),((y*z : B) : FreeAmalgam R)⁆,hBZ (commutator_mem_commutator x.property (B.mul_mem y.property z.property))⟩ : Z) =
          ⟨⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆,hBZ (commutator_mem_commutator x.property y.property)⟩ *
          ⟨⁅(x : FreeAmalgam R),(z : FreeAmalgam R)⁆,hBZ (commutator_mem_commutator x.property z.property)⟩ := by
        apply Subtype.ext
        have hc := hZB (hBZ (commutator_mem_commutator x.property z.property)) y y.property
        change ⁅(x : FreeAmalgam R),(y : FreeAmalgam R)*(z : FreeAmalgam R)⁆ = _
        rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc _ (y : FreeAmalgam R),hc]
        simp only [coe_mul,mul_assoc,mul_inv_cancel,mul_one]
      change q _ = q _ * q _
      rw [he,map_mul] }
  let β : B →* (B →* E) := {
    toFun := row
    map_one' := by
      apply MonoidHom.ext
      intro y
      change q _ = 1
      rw [show (⟨⁅((1 : B) : FreeAmalgam R),(y : FreeAmalgam R)⁆,_⟩ : Z) = 1 from Subtype.ext (by simp),map_one]
    map_mul' x y := by
      apply MonoidHom.ext
      intro z
      have he : (⟨⁅((x*y : B) : FreeAmalgam R),(z : FreeAmalgam R)⁆,hBZ (commutator_mem_commutator (B.mul_mem x.property y.property) z.property)⟩ : Z) =
          ⟨⁅(y : FreeAmalgam R),(z : FreeAmalgam R)⁆,hBZ (commutator_mem_commutator y.property z.property)⟩ *
          ⟨⁅(x : FreeAmalgam R),(z : FreeAmalgam R)⁆,hBZ (commutator_mem_commutator x.property z.property)⟩ := by
        apply Subtype.ext
        have hc := hZB (hBZ (commutator_mem_commutator y.property z.property)) x x.property
        change ⁅(x : FreeAmalgam R)*(y : FreeAmalgam R),(z : FreeAmalgam R)⁆ = _
        rw [commutatorElement_mul_left_eq_conj_mul,hc,mul_inv_cancel_right]
        rfl
      change q _ = q _ * q _
      rw [he,map_mul,mul_comm] }
  obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm singer)
  have hmg : common.natural.marking (source.projection m) = singer := by simp [hm]
  let a : MulAut B := B.normalizerMonoidHom ⟨embedM R m,s.normalized ⟨m,rfl⟩⟩
  have ha (x : B) : ((a x : B) : FreeAmalgam R) =
      embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ := rfl
  have hcoords (x : B) : (s.quotient (a x)).toAdd =
      (dual singer (s.quotient x).toAdd.1,dual singer (s.quotient x).toAdd.2) := by
    simpa only [hmg,if_true] using s.action m x (a x) (ha x)
  have hnorm (x : B) : ((a (a (a x)) * a (a x) * x : B) : FreeAmalgam R) ∈ F := by
    have hk : a (a (a x)) * a (a x) * x ∈ s.quotient.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      change (s.quotient (a (a (a x)) * a (a x) * x)).toAdd = 0
      simp only [map_mul,toAdd_mul,hcoords]
      exact Prod.ext (dual_singer_cubic _) (dual_singer_cubic _)
    rwa [s.kernel] at hk
  have hact (x y : B) : β (a x) (a y) = β x y := by
    apply hfixed m
    change ⁅((a x : B) : FreeAmalgam R),((a y : B) : FreeAmalgam R)⁆ = _
    rw [ha,ha,← conjugate_commutatorElement]
  have hleft (x : B) : β (a (a (a x)) * a (a x) * x) = 1 := by
    apply MonoidHom.ext
    intro y
    change q _ = 1
    have he : ⁅((a (a (a x)) * a (a x) * x : B) : FreeAmalgam R),(y : FreeAmalgam R)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hF (hnorm x) y y.property).symm
    rw [show (⟨_,_⟩ : Z) = 1 from Subtype.ext he,map_one]
  have hright (x y : B) : β x (a (a (a y)) * a (a y) * y) = 1 := by
    change q _ = 1
    have he : ⁅(x : FreeAmalgam R),((a (a (a y)) * a (a y) * y : B) : FreeAmalgam R)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hF (hnorm y) x x.property)
    rw [show (⟨_,_⟩ : Z) = 1 from Subtype.ext he,map_one]
  have hzero := binary_reciprocal_pairing_zero a β hact hleft hright hsquare
  apply commutator_le.mpr
  intro x hx y hy
  have h := hzero ⟨x,hx⟩ ⟨y,hy⟩
  change q ⟨⁅x,y⁆,_⟩ = 1 at h
  have hk := MonoidHom.mem_ker.mpr h
  rwa [hker] at hk

/-- The second-hat commutator has no component in the locally fixed Z-summand. -/
theorem second_derived_le_U (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ ≤ U R (alpha R) := by
  let B := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let Z₀ := Z R (alpha R)
  let U₀ := U R (alpha R)
  let P := stabilizer R (alpha R)
  let F := Z₀ ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
  let := geometry.Z_elementary (by rw [earlier.distance]; decide) (alpha R) rfl
  let N := U₀.subgroupOf Z₀
  let : N.Normal := normal_of_isMulCommutative N
  let E := Z₀ ⧸ N
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.quotient N
  let : CommGroup E := IsMulCommutative.instCommGroup
  let q : Z₀ →* E := QuotientGroup.mk' N
  have hB : B ≤ Q R (alpha R) := (second_le_core_sup_Z common earlier p).trans
    (sup_le (DistanceTwo.core_le_Q _) (by
      rw [← common.X_eq_Z _ rfl]; exact omegaCenter_le _))
  have hZP : Z₀ ≤ P := Z_le_stabilizer R _
  have hFC : F ≤ centralizer (P : Set (FreeAmalgam R)) := by
    intro z hz
    exact ((source.X_fixed_eq_stabilizer_fixed (alpha R) rfl).le
      ⟨by rw [common.X_eq_Z _ rfl]; exact hz.1,hz.2⟩).2
  have hPU : P ≤ normalizer U₀ := U_normalized _
  have hZcomm : ⁅Z₀,P⁆ ≤ U₀ := by
    have hZpre : Z₀ ≤ commutatorPreimage P P U₀ := by
      rw [show Z₀ = U₀ ⊔ F from common.decomposition]
      apply sup_le
      · exact le_commutatorPreimage ((U_le_Z R _).trans hZP)
          (le_normalizer_iff_commutator_le_left.mp hPU)
      · exact le_commutatorPreimage (inf_le_left.trans hZP)
          ((commutator_eq_bot_iff_le_centralizer.mpr hFC).le.trans bot_le)
    exact (commutator_mono hZpre le_rfl).trans
      (commutator_commutatorPreimage_le P P U₀ hPU)
  obtain ⟨s⟩ := Quotients.SecondLayer.OrbitSource.marked_pair common earlier p
  apply marked_dual_pair_derived_le common s
    ((second_center common earlier p).symm.le.trans inf_le_right)
    ((commutator_mono le_rfl hB).trans
      (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatW_commutator)
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ rfl)).trans
      (centralizer_le hB)) q (QuotientGroup.ker_mk' N)
  · intro m x y hy
    apply mul_inv_eq_one.mp
    rw [← map_inv,← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    change (y : FreeAmalgam R) * (x : FreeAmalgam R)⁻¹ ∈ U₀
    rw [hy]
    change ⁅embedM R m,(x : FreeAmalgam R)⁆ ∈ U₀
    rw [commutator_comm] at hZcomm
    exact hZcomm (commutator_mem_commutator (by
      simp only [P,alpha,stabilizer_m_base]; exact ⟨m,rfl⟩) x.property)
  · intro e
    exact (pow_two e).symm.trans
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) e)

/-- The second hat has precisely the original natural subgroup as its derived subgroup. -/
theorem second_derived_eq_U (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ = U R (alpha R) := by
  let B := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let D := ⁅B,B⁆
  have hDU : D ≤ U R (alpha R) := second_derived_le_U common earlier p
  have hne : D ≠ ⊥ := second_nonabelian common earlier p
  obtain ⟨u₀,hu₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let x : FreeAmalgam R := u₀
  have hx : x ∈ D := u₀.property
  have hxne : x ≠ 1 := fun he => hu₀ (Subtype.ext he)
  let u : U R (alpha R) := ⟨x,hDU hx⟩
  have hu : (common.natural.equiv u).toAdd ≠ 0 := by
    intro he
    have he' : common.natural.equiv u = 1 := Multiplicative.toAdd.injective he
    have h := common.natural.equiv.injective (he'.trans (map_one common.natural.equiv).symm)
    exact hxne (congrArg Subtype.val h)
  have hnorm : Mbar R ≤ normalizer D := by
    intro g hg
    have hb : g ∈ normalizer B := hatW_normalized R _ _ _ (by
      simpa only [alpha,stabilizer_m_base] using hg)
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [D]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp hb]
  apply le_antisymm hDU
  intro y hy
  by_cases he : y = 1
  · simpa only [he] using D.one_mem
  let v : U R (alpha R) := ⟨y,hy⟩
  have hv : (common.natural.equiv v).toAdd ≠ 0 := by
    intro hz
    have hz' : common.natural.equiv v = 1 := Multiplicative.toAdd.injective hz
    have h := common.natural.equiv.injective (hz'.trans (map_one common.natural.equiv).symm)
    exact he (congrArg Subtype.val h)
  obtain ⟨g,hg⟩ := natural_orbit hu hv
  obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmark : common.natural.marking (source.projection m) = g := by simp [hm]
  let w : U R (alpha R) := ⟨embedM R m * x * (embedM R m)⁻¹,
    le_normalizer_iff.mp common.natural.normalized _ ⟨m,rfl⟩ _ (hDU hx)⟩
  have hw : w = v := by
    apply common.natural.equiv.injective
    apply Multiplicative.toAdd.injective
    rw [common.natural.action m u w rfl,hmark]
    exact hg
  have hwD := le_normalizer_iff.mp hnorm _ ⟨m,rfl⟩ _ hx
  have hwy : (w : FreeAmalgam R) = y := congrArg Subtype.val hw
  exact hwy ▸ hwD

/-- The natural subgroup occurs in the actual core derived subgroup, without
assuming the full fixed-factor identification. -/
theorem U_le_core_derived (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    U R (alpha R) ≤ ⁅core R (alpha R),core R (alpha R)⁆ := by
  let K := core R (alpha R)
  let Z₀ := Z R (alpha R)
  have hZ : Z₀ ≤ centralizer (K : Set (FreeAmalgam R)) :=
    Quotients.FirstDirect.Z_centralizes_core common earlier
  have hZabel : Z₀ ≤ centralizer (Z₀ : Set (FreeAmalgam R)) := by
    let := geometry.Z_elementary (by rw [earlier.distance]; decide) (alpha R) rfl
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hZC : Z₀ ≤ centralizer ((Z₀ ⊔ K : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hZabel) (le_centralizer_iff.mp hZ))
  have hnorm : K ≤ normalizer ((Z₀ ⊔ K : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    le_sup_right.trans (Z₀ ⊔ K).le_normalizer
  have he : ⁅Z₀ ⊔ K,Z₀ ⊔ K⁆ = ⁅K,K⁆ := by
    rw [← commutator_eq_of_centralizing_sup rfl hZC hnorm,commutator_comm,
      ← commutator_eq_of_centralizing_sup rfl hZ K.le_normalizer]
  rw [← second_derived_eq_U common earlier p]
  have hb := second_le_core_sup_Z common earlier p
  rw [sup_comm] at hb
  exact (commutator_mono hb hb).trans_eq he

/-- The complete moving radius layer occurs in the original core derived group.
The already proved first-dual occurrence and this exact natural kernel remove Z. -/
theorem moving_le_core_derived (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Vcirc R (alpha R) ≤ ⁅core R (alpha R),core R (alpha R)⁆ := by
  let K := core R (alpha R)
  let D := ⁅K,K⁆
  let P := stabilizer R (alpha R)
  have hnorm : P ≤ normalizer D := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [D]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (DistanceTwo.core_normalized _ hg)]
  have hpre : D ⊔ Z R (alpha R) ≤
      commutatorPreimage P (Ltilde R (alpha R)) D := by
    apply sup_le
    · exact le_commutatorPreimage ((commutator_le_self K).trans
        ((DistanceTwo.core_le_Q _).trans (fun _ hx => hx.1)))
        (le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer _).trans hnorm))
    · exact le_commutatorPreimage (Z_le_stabilizer R _)
        (U_le_core_derived common earlier p)
  have hfirst := first_le_core_derived_sup_Z common earlier p
  have hmove : Vcirc R (alpha R) ≤
      hatV R (alpha R) (p.walk.getVert 6) := by
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_left
  have hid : ⁅Vcirc R (alpha R),Ltilde R (alpha R)⁆ = Vcirc R (alpha R) := by
    let A := (V R (alpha R)).subgroupOf P
    let := finite_stabilizer R (alpha R)
    let : A.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R _)
    let := V_elementary_of_four_lt R (a := alpha R) rfl (by rw [earlier.distance]; decide)
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf
      (geometry.V_local (alpha R) rfl common.large_distance)
    have he := commutator_isPPerfect_idempotent (pResidual 2 P) A
      (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 A) le_normalizer_of_normal
    have hm := congrArg (fun C : Subgroup P => C.map P.subtype) he
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le
      (geometry.V_local (alpha R) rfl common.large_distance)] at hm
    exact hm
  rw [← hid]
  exact (commutator_mono (hmove.trans (hfirst.trans hpre)) le_rfl).trans
    (commutator_commutatorPreimage_le P (Ltilde R (alpha R)) D hnorm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
