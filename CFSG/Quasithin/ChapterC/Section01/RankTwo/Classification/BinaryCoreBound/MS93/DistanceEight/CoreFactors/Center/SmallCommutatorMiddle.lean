module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.SecondLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Singer
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Small commutators in the actual second hat layer

The marked second quotient is a pair of dual binary three-spaces. A locally
normalized subgroup with commutator of order at most two against the second
hat centralizes that hat: its commutator image is fixed by the whole local
group, while the marked Singer action has mutually incompatible reciprocal
relations on the two slots of the commutator pairing. The actual second-hat
center is the first hat, giving the middle step of the quotient-center proof.

All quotient coordinates and actors are those of the source construction.
The argument uses neither a classification of invariant subspaces nor an
identification of the full original fixed factor with H.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), pp.898--899;
Aschbacher--Smith, the large binary branch of 15.3.31, printed p.1132.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative

private theorem reciprocal_pairing_zero {D W E : Type*}
    [Group D] [Group W] [CommGroup E]
    (a : MulAut D) (b : MulAut W) (β : D →* (W →* E))
    (hact : ∀ x y, β (a x) (b y) = β x y)
    (hleft : ∀ x, β (a (a (a x)) * a (a x) * x) = 1)
    (hright : ∀ x y, β x (b (b (b y)) * b (b y) * y) = 1)
    (hsquare : ∀ e : E, e * e = 1) : ∀ x y, β x y = 1 := by
  have hstep (x : D) (y : W) : β x (b y) = β x (b (b y)) := by
    have hl := congrArg (fun f : W →* E => f (b (b (b y)))) (hleft x)
    simp only [map_mul, MonoidHom.mul_apply, MonoidHom.one_apply] at hl
    rw [hact (a (a x)) (b (b y)), hact (a x) (b y), hact x y,
      hact (a x) (b (b y)), hact x (b y)] at hl
    have hr := hright x y
    simp only [map_mul] at hr
    apply mul_left_cancel (a := β x y * β x (b (b (b y))))
    calc
      _ = β x y * β x (b y) * β x (b (b (b y))) := by ac_rfl
      _ = 1 := hl
      _ = β x (b (b (b y))) * β x (b (b y)) * β x y := hr.symm
      _ = _ := by ac_rfl
  have hfixed (x : D) (y : W) : β x (b y) = β x y := by
    simpa only [b.apply_symm_apply] using (hstep x (b.symm y)).symm
  intro x y
  have h := hright x y
  simp only [map_mul,hfixed] at h
  rwa [hsquare,one_mul] at h


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open DistanceFour.Linear
open DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Singer

private theorem singer_inverse : singer⁻¹ = (⟨!![1,1,0; 0,0,1; 1,0,0], by decide⟩ : S) := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem dual_singer_relation (v : W) :
    dual singer (dual singer (dual singer v)) + dual singer (dual singer v) + v = 0 := by
  have h : ∀ v : W,
      dual singer (dual singer (dual singer v)) + dual singer (dual singer v) + v = 0 := by
    simp only [dual,singer_inverse]
    decide +kernel
  exact h v

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open Higher DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem marked_pair_small_commutator
    {common : CommonFacts R source geometry} {B F D : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common B F true)
    (hF : F ≤ centralizer (B : Set (FreeAmalgam R)))
    (hDB : D ≤ B) (hD : Mbar R ≤ normalizer D)
    (hcard : Nat.card (⁅D,B⁆ : Subgroup (FreeAmalgam R)) ≤ 2) : ⁅D,B⁆ = ⊥ := by
  let E := ⁅D,B⁆
  have hEB : E ≤ B := (Subgroup.commutator_le_sup D B).trans (sup_le hDB le_rfl)
  let := finite_stabilizer R (alpha R)
  let : Finite B := Finite.of_injective (inclusion s.local_group)
    (inclusion_injective s.local_group)
  let : Finite E := Finite.of_injective (inclusion hEB) (inclusion_injective hEB)
  have hepos := Nat.card_pos (α := E)
  have he : Nat.card E = 1 ∨ Nat.card E = 2 := by change Nat.card E ≤ 2 at hcard; omega
  rcases he with he | he
  · exact card_eq_one.mp he
  have hNE := normalizer_le_centralizer_of_card_two E he
  have hBE : B ≤ centralizer (E : Set (FreeAmalgam R)) :=
    (normalizer_commutator_ge_right D B).trans hNE
  have hEc : E ≤ centralizer (E : Set (FreeAmalgam R)) := hEB.trans hBE
  let : IsMulCommutative E := le_centralizer_iff_isMulCommutative.mp hEc
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hME : Mbar R ≤ centralizer (E : Set (FreeAmalgam R)) := by
    apply le_trans ?_ hNE
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change E.map (MulAut.conj g).toMonoidHom = E
    dsimp only [E]
    rw [map_commutator, MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (hD hg),
      mem_normalizer_iff_map_conj_eq.mp (s.normalized hg)]
  let row (x : D) : B →* E := {
    toFun y := ⟨⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆,
      commutator_mem_commutator x.property y.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' y z := by
      apply Subtype.ext
      change ⁅(x : FreeAmalgam R),(y : FreeAmalgam R) * z⁆ =
        ⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆ * ⁅(x : FreeAmalgam R),(z : FreeAmalgam R)⁆
      have hc := hBE y.property _ (commutator_mem_commutator x.property z.property)
      rw [commutatorElement_mul_right_eq_mul_conj]
      rw [mul_assoc _ (y : FreeAmalgam R), ← hc]
      group }
  let β : D →* (B →* E) := {
    toFun := row
    map_one' := by ext y; simp [row]
    map_mul' x y := by
      ext z
      change ⁅(x : FreeAmalgam R) * y,(z : FreeAmalgam R)⁆ =
        ⁅(x : FreeAmalgam R),(z : FreeAmalgam R)⁆ * ⁅(y : FreeAmalgam R),(z : FreeAmalgam R)⁆
      have hc := hBE (hDB x.property) _ (commutator_mem_commutator y.property z.property)
      rw [commutatorElement_mul_left_eq_conj_mul, ← hc, mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (row y z) (row x z)) }
  obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm singer)
  have hmg : common.natural.marking (source.projection m) = singer := by simp [hm]
  have hmbar : embedM R m ∈ Mbar R := ⟨m,rfl⟩
  let a : MulAut D := D.normalizerMonoidHom ⟨embedM R m,hD hmbar⟩
  let b : MulAut B := B.normalizerMonoidHom ⟨embedM R m,s.normalized hmbar⟩
  have ha (x : D) : ((a x : D) : FreeAmalgam R) =
      embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ := rfl
  have hb (x : B) : ((b x : B) : FreeAmalgam R) =
      embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ := rfl
  have hcoords (x : B) : (s.quotient (b x)).toAdd =
      (dual singer (s.quotient x).toAdd.1,dual singer (s.quotient x).toAdd.2) := by
    simpa only [hmg, if_true] using s.action m x (b x) (hb x)
  have hnorm (x : B) : ((b (b (b x)) * b (b x) * x : B) : FreeAmalgam R) ∈ F := by
    have hk : b (b (b x)) * b (b x) * x ∈ s.quotient.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      change (s.quotient (b (b (b x)) * b (b x) * x)).toAdd = 0
      simp only [map_mul, toAdd_mul, hcoords]
      apply Prod.ext
      · exact dual_singer_relation _
      · exact dual_singer_relation _
    rwa [s.kernel] at hk
  have hβact (x : D) (y : B) : β (a x) (b y) = β x y := by
    apply Subtype.ext
    change ⁅((a x : D) : FreeAmalgam R),((b y : B) : FreeAmalgam R)⁆ =
      ⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆
    rw [ha,hb,← conjugate_commutatorElement]
    have hc := hME hmbar _ (commutator_mem_commutator x.property y.property)
    rw [← hc,mul_inv_cancel_right]
  have hleft (x : D) : β (a (a (a x)) * a (a x) * x) = 1 := by
    apply MonoidHom.ext
    intro y
    apply Subtype.ext
    change ⁅((a (a (a x)) * a (a x) * x : D) : FreeAmalgam R),(y : FreeAmalgam R)⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    have hin : inclusion hDB (a (a (a x)) * a (a x) * x) =
        b (b (b (inclusion hDB x))) * b (b (inclusion hDB x)) * inclusion hDB x := rfl
    have hxF := hnorm (inclusion hDB x)
    rw [← hin] at hxF
    exact (hF hxF y y.property).symm
  have hright (x : D) (y : B) : β x (b (b (b y)) * b (b y) * y) = 1 := by
    apply Subtype.ext
    change ⁅(x : FreeAmalgam R),((b (b (b y)) * b (b y) * y : B) : FreeAmalgam R)⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hF (hnorm y) x (hDB x.property))
  have hz := reciprocal_pairing_zero a b β hβact hleft hright (fun e => by
    simpa only [he,pow_two] using (pow_card_eq_one' (x := e)))
  apply le_bot_iff.mp
  apply commutator_le.mpr
  intro x hx y hy
  exact congrArg Subtype.val (hz ⟨x,hx⟩ ⟨y,hy⟩)

/-- A locally normalized subgroup of the second hat cannot have a
nontrivial commutator of order at most two with that hat. The actual doubled
dual quotient and one marked Singer element force the pairing to vanish. -/
theorem second_small_commutator_eq_bot
    (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    {D : Subgroup (FreeAmalgam R)}
    (hD : D ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
    (hn : stabilizer R (alpha R) ≤ normalizer D)
    (hc : Nat.card (⁅D,hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ :
      Subgroup (FreeAmalgam R)) ≤ 2) :
    ⁅D,hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ = ⊥ := by
  obtain ⟨s⟩ := Quotients.SecondLayer.OrbitSource.marked_pair common earlier p
  apply marked_pair_small_commutator s ?_ hD ?_ hc
  · exact (second_center common earlier p).symm.le.trans inf_le_right
  · simpa only [alpha,stabilizer_m_base] using hn

/-- The middle step in the quotient-center argument: every locally normalized
subgroup whose second-hat commutator has order at most two lies in the first
hat. No first-hat intersection or original-core centrality premise is needed. -/
theorem second_small_commutator_le_first
    (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    {D : Subgroup (FreeAmalgam R)}
    (hD : D ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
    (hn : stabilizer R (alpha R) ≤ normalizer D)
    (hc : Nat.card (⁅D,hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ :
      Subgroup (FreeAmalgam R)) ≤ 2) :
    D ≤ hatV R (alpha R) (p.walk.getVert 6) := by
  rw [← second_center common earlier p]
  exact le_inf hD (commutator_eq_bot_iff_le_centralizer.mp
    (second_small_commutator_eq_bot common earlier p hD hn hc))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
