module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.NaturalPair
public import Theory.GroupTheory.AbelianQuotientFixedSubgroup

/-!
# The first layer in the actual core derived subgroup

The first hat layer occurs in the core derived subgroup modulo Z. If its
irreducible dual quotient were missed, the core would be abelian modulo Z.
Commutation with a fixed element of the full third hat would then give an
SL3(2)-equivariant map from the actual natural pair to the first dual layer.
Such a map vanishes. The three-subgroups lemma would consequently make the
entire first dual layer fixed, contradicting its marked source action.

This uses the literal subgroup quotients and the CommonFacts marking. It
requires no splitting of the full third layer and no centrality assumption
on its additional fixed part. The result is the opening input for the
small-displacement, or no-new-center, argument on the original MS core.

Source: consequences of the marked layers and commutator equalities in
Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895,898--900.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open NormalizerTransfer PathCentrality Higher DistanceFour.Linear

private theorem natural_dual_zero (f : W → W)
    (hf : ∀ (g : S) (v : W), f (g.val.mulVec v) = dual g (f v)) :
    ∀ v, f v = 0 := by
  apply equivariantDualMap_zero f
  intro g v
  have hi : (Matrix.SpecialLinearGroup.transpose g⁻¹)⁻¹ =
      Matrix.SpecialLinearGroup.transpose g := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (g⁻¹).val.transpose * g.val.transpose = 1
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have h := hf (Matrix.SpecialLinearGroup.transpose g⁻¹) v
  simpa only [dual, hi, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.transpose_transpose] using h


private theorem naturalPair_dual_zero
    (f : Multiplicative (W × W) →* Multiplicative W)
    (hf : ∀ (g : S) (v : W × W),
      (f (Multiplicative.ofAdd (g.val.mulVec v.1,g.val.mulVec v.2))).toAdd =
        dual g (f (Multiplicative.ofAdd v)).toAdd) : f = 1 := by
  have hleft := natural_dual_zero (fun v => (f (Multiplicative.ofAdd (v,0))).toAdd)
    (fun g v => by simpa only [Matrix.mulVec_zero] using hf g (v,0))
  have hright := natural_dual_zero (fun v => (f (Multiplicative.ofAdd (0,v))).toAdd)
    (fun g v => by simpa only [Matrix.mulVec_zero] using hf g (0,v))
  apply MonoidHom.ext
  intro v
  apply Multiplicative.toAdd.injective
  have he : v = Multiplicative.ofAdd (v.toAdd.1,0) * Multiplicative.ofAdd (0,v.toAdd.2) := by
    apply Multiplicative.toAdd.injective
    simp
  rw [he,map_mul]
  change (f (Multiplicative.ofAdd (v.toAdd.1,0))).toAdd +
    (f (Multiplicative.ofAdd (0,v.toAdd.2))).toAdd = 0
  rw [hleft,hright,add_zero]

section GroupPairing
variable {G : Type*} [Group G] {A F Z : Subgroup G}
    (q : F →* Multiplicative W) (hq : q.ker = Z.subgroupOf F)

include hq in
private theorem section_eq (x y : F) (h : (x : G) * (y : G)⁻¹ ∈ Z) : q x = q y := by
  apply mul_inv_eq_one.mp
  rw [← map_inv,← map_mul]
  exact MonoidHom.mem_ker.mp (hq ▸ h)

include hq in
private theorem section_conj (hAF : A ≤ normalizer F)
    (hFA : ⁅F,A⁆ ≤ Z) (a : A) (d : F) :
    q ⟨(a : G) * (d : G) * (a : G)⁻¹,
      le_normalizer_iff.mp hAF _ a.property _ d.property⟩ = q d := by
  apply section_eq q hq
  change ⁅(a : G),(d : G)⁆ ∈ Z
  rw [commutator_comm] at hFA
  exact hFA (commutator_mem_commutator a.property d.property)

private noncomputable def layerPairing (hAF : A ≤ normalizer F)
    (hAA : ⁅A,A⁆ ≤ F) (hFA : ⁅F,A⁆ ≤ Z) :
    A →* (A →* Multiplicative W) where
  toFun a := {
    toFun b := q ⟨⁅(a : G),(b : G)⁆,hAA (commutator_mem_commutator a.property b.property)⟩
    map_one' := by
      change q ⟨⁅(a : G),1⁆,_⟩ = 1
      rw [show (⟨⁅(a : G),1⁆,_⟩ : F) = 1 from Subtype.ext (by simp),map_one]
    map_mul' b c := by
      have he : (⟨⁅(a : G),(b : G)*(c : G)⁆,
        hAA (commutator_mem_commutator a.property (A.mul_mem b.property c.property))⟩ : F) =
        ⟨⁅(a : G),(b : G)⁆,hAA (commutator_mem_commutator a.property b.property)⟩ *
        ⟨(b : G)*⁅(a : G),(c : G)⁆*(b : G)⁻¹,
          le_normalizer_iff.mp hAF _ b.property _
            (hAA (commutator_mem_commutator a.property c.property))⟩ := by
        apply Subtype.ext
        simpa only [coe_mul,mul_assoc] using
          commutatorElement_mul_right_eq_mul_conj (a : G) (b : G) (c : G)
      change q ⟨⁅(a : G),(b : G)*(c : G)⁆,_⟩ = q _ * q _
      rw [he,map_mul,section_conj q hq hAF hFA b
        ⟨⁅(a : G),(c : G)⁆,hAA (commutator_mem_commutator a.property c.property)⟩] }
  map_one' := by
    apply MonoidHom.ext
    intro b
    change q ⟨⁅(1 : G),(b : G)⁆,_⟩ = 1
    rw [show (⟨⁅(1 : G),(b : G)⁆,_⟩ : F) = 1 from Subtype.ext (by simp),map_one]
  map_mul' a b := by
    apply MonoidHom.ext
    intro c
    have he : (⟨⁅(a : G)*(b : G),(c : G)⁆,
      hAA (commutator_mem_commutator (A.mul_mem a.property b.property) c.property)⟩ : F) =
      ⟨(a : G)*⁅(b : G),(c : G)⁆*(a : G)⁻¹,
        le_normalizer_iff.mp hAF _ a.property _
          (hAA (commutator_mem_commutator b.property c.property))⟩ *
      ⟨⁅(a : G),(c : G)⁆,hAA (commutator_mem_commutator a.property c.property)⟩ := by
      apply Subtype.ext
      exact commutatorElement_mul_left_eq_conj_mul (a : G) (b : G) (c : G)
    change q ⟨⁅(a : G)*(b : G),(c : G)⁆,_⟩ = q _ * q _
    rw [he,map_mul,section_conj q hq hAF hFA a
      ⟨⁅(b : G),(c : G)⁆,hAA (commutator_mem_commutator b.property c.property)⟩,mul_comm]

end GroupPairing

variable {M : Type*} [Group M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}
  {common : CommonFacts R source geometry}

private theorem marked_mixed_commutator_le
    {A B C F N Z : Subgroup (FreeAmalgam R)}
    (s : MarkedDualSection source common F Z)
    (t : MarkedPairSection source common B N false)
    (hAn : Mbar R ≤ normalizer A) (hAF : A ≤ normalizer F)
    (hAA : ⁅A,A⁆ ≤ F) (hFA : ⁅F,A⁆ ≤ Z)
    (hBA : B ≤ A) (hBC : B ≤ C) (hCC : ⁅C,C⁆ ≤ Z)
    (hNA : ⁅N,A⁆ ≤ Z) (hAP : ⁅A,Mbar R⁆ ≤ C) : ⁅A,B⁆ ≤ Z := by
  let pair : A →* (A →* Multiplicative W) :=
    layerPairing (G := FreeAmalgam R) (A := A) (F := F) (Z := Z)
      s.quotient s.kernel hAF hAA hFA
  let raw (a : A) : B →* Multiplicative W := (pair a).comp (inclusion hBA)
  have hraw (a : A) (b : B) : raw a b = s.quotient
      ⟨⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆,
        hAA (commutator_mem_commutator a.property (hBA b.property))⟩ := rfl
  have hkill (a : A) : t.quotient.ker ≤ (raw a).ker := by
    intro b hb
    rw [t.kernel] at hb
    apply MonoidHom.mem_ker.mpr
    rw [hraw]
    apply MonoidHom.mem_ker.mp
    rw [s.kernel]
    change ⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆ ∈ Z
    rw [commutator_comm] at hNA
    exact hNA (commutator_mem_commutator a.property hb)
  let f (a : A) : Multiplicative (W × W) →* Multiplicative W :=
    t.quotient.liftOfSurjective t.onto ⟨raw a,hkill a⟩
  have hf (a : A) (b : B) : f a (t.quotient b) = raw a b :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hfzero (a : A) : f a = 1 := by
    apply naturalPair_dual_zero
    intro g v
    obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm g)
    have hmark : common.natural.marking (source.projection m) = g := by simp only [hm,MulEquiv.apply_symm_apply]
    obtain ⟨b,hb⟩ := t.onto (Multiplicative.ofAdd v)
    let a' : A := ⟨embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp hAn _ ⟨m,rfl⟩ _ a.property⟩
    let b' : B := ⟨embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp t.normalized _ ⟨m,rfl⟩ _ b.property⟩
    have hb' : t.quotient b' = Multiplicative.ofAdd (g.val.mulVec v.1,g.val.mulVec v.2) := by
      apply Multiplicative.toAdd.injective
      simpa only [hmark,hb,Bool.false_eq_true,reduceIte,toAdd_ofAdd] using t.action m b b' rfl
    have hd : ((a' * a⁻¹ : A) : FreeAmalgam R) ∈ C := by
      change ⁅embedM R m,(a : FreeAmalgam R)⁆ ∈ C
      rw [commutator_comm] at hAP
      exact hAP (commutator_mem_commutator ⟨m,rfl⟩ a.property)
    have hrow : raw a' b' = raw a b' := by
      have hz : pair (a' * a⁻¹) (inclusion hBA b') = 1 := by
        change s.quotient _ = 1
        apply MonoidHom.mem_ker.mp
        rw [s.kernel]
        exact hCC (commutator_mem_commutator hd (hBC b'.property))
      change pair a' (inclusion hBA b') = pair a (inclusion hBA b')
      simpa only [map_mul,map_inv,MonoidHom.mul_apply,MonoidHom.inv_apply,
        mul_inv_eq_one] using hz
    have he : (raw a' b').toAdd = dual g (raw a b).toAdd := by
      rw [hraw,hraw]
      rw [← hmark]
      apply s.action m
      change ⁅embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
        embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹⁆ = _
      group
    rw [← hb',← hb,hf,hf,← hrow]
    exact he
  apply commutator_le.mpr
  intro a ha b hb
  have hz := hf ⟨a,ha⟩ ⟨b,hb⟩
  rw [hfzero] at hz
  have hk : (⟨⁅a,b⁆,hAA (commutator_mem_commutator ha (hBA hb))⟩ : F) ∈ s.quotient.ker :=
    MonoidHom.mem_ker.mpr hz.symm
  rwa [s.kernel] at hk


private theorem marked_dual_nontrivial
    {F Z : Subgroup (FreeAmalgam R)} (s : MarkedDualSection source common F Z) :
    ¬ ⁅F,Mbar R⁆ ≤ Z := by
  intro h
  let v : W := ![1,0,0]
  let w : W := ![0,1,0]
  have hv : v ≠ 0 := by decide
  have hw : w ≠ 0 := by decide
  have hne : v ≠ w := by decide
  obtain ⟨g,hg⟩ := dual_orbit hv hw
  obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmark : common.natural.marking (source.projection m) = g := by
    simp only [hm,MulEquiv.apply_symm_apply]
  obtain ⟨a,ha⟩ := s.onto (Multiplicative.ofAdd v)
  let b : F := ⟨embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp s.normalized _ ⟨m,rfl⟩ _ a.property⟩
  have he : s.quotient b = s.quotient a := by
    apply section_eq s.quotient s.kernel
    change ⁅embedM R m,(a : FreeAmalgam R)⁆ ∈ Z
    rw [commutator_comm] at h
    exact h (commutator_mem_commutator ⟨m,rfl⟩ a.property)
  have hh := s.action m a b rfl
  rw [he,ha,hmark] at hh
  exact hne (hh.trans hg)

variable [Finite M]

private theorem core_derived_not_le_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ¬ ⁅core R (alpha R),core R (alpha R)⁆ ≤ Z R (alpha R) := by
  let A := hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)
  let F := hatV R (alpha R) (p.walk.getVert 6)
  let W₀ := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let K := core R (alpha R)
  let Z₀ := Z R (alpha R)
  let P := stabilizer R (alpha R)
  let C := K ⊔ Z₀
  let B := K ⊔ W₀
  let path := Early.Orbit.SourceApplications.higherPath geometry p
  have hP : P = Mbar R := by simp only [P,alpha,stabilizer_m_base]
  have hAQ : A ≤ Q R (alpha R) := path.hatSix_le_Q earlier
  have hAlocal : A ≤ P := hAQ.trans (fun _ hx => hx.1)
  have hKlocal : K ≤ P := fun _ hx => (DistanceTwo.core_le_Q _ hx).1
  have hKA : K ≤ A := Early.Orbit.Source.Complete.core_le_third_hat common earlier p
  have hWA : W₀ ≤ A := OrbitGeometry.hatW_le_hatSix
    (p.even_color (i := 8) (by decide) (by decide))
    (by rw [SimpleGraph.dist_comm]; exact path.two_step_distances.2.2)
  have hFW : F ≤ W₀ := Quotients.SecondLayer.lower_le_second path
  have hWQ : ⁅W₀,Q R (alpha R)⁆ ≤ Z₀ :=
    (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatW_commutator
  have hFZ : F ≤ C := by
    change hatV R (alpha R) (p.walk.getVert 6) ≤ K ⊔ Z₀
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact sup_le ((Vcirc_le_core rfl common.large_distance).trans le_sup_left) le_sup_right
  have hWC : W₀ ≤ C := second_le_core_sup_Z common earlier p
  have hPA : P ≤ normalizer A := hatSix_normalized R _ _ _ _
  have hPZ : P ≤ normalizer Z₀ := Z_normalized R _
  have hPC : P ≤ normalizer C :=
    (le_inf (DistanceTwo.core_normalized _) hPZ).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZAc : Z₀ ≤ centralizer (A : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ rfl)).trans
      (centralizer_le hAQ)
  have hFA : ⁅F,A⁆ ≤ Z₀ := (commutator_mono hFW hAQ).trans hWQ
  have hAA : ⁅A,A⁆ ≤ F := le_sup_left.trans
    (Higher.OrbitGeometry.Source.commutator_layers common earlier p).2.le
  have hAP : ⁅A,P⁆ ≤ C := by
    let D := commutatorPreimage P A C
    have hLD : Ltilde R (alpha R) ≤ D := by
      apply le_commutatorPreimage (Ltilde_le_stabilizer _)
      rw [commutator_comm,← core_eq_third_residual common earlier p]
      exact le_sup_left
    have hQD : Q R (alpha R) ≤ D := by
      apply le_commutatorPreimage (show Q R (alpha R) ≤ P from fun _ hx => hx.1)
      rw [commutator_comm]
      exact (Higher.OrbitGeometry.Source.Q_commutator_le common earlier p).trans hFZ
    have hPD : P ≤ D := by
      change stabilizer R (alpha R) ≤ D
      rw [← source.local_generation _ rfl]
      exact sup_le hLD hQD
    rw [commutator_comm]
    exact (commutator_mono hPD le_rfl).trans
      (commutator_commutatorPreimage_le P A C hPC)
  intro hKK
  have hCC : ⁅C,C⁆ ≤ Z₀ := by
    simpa only [C,sup_comm] using commutator_sup_le_of_normalized_derived
      Z₀ K (hKlocal.trans hPZ) hKK
  obtain ⟨s⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  obtain ⟨t⟩ := core_second_marked_natural_pair common earlier p
  have hAB : ⁅A,B⁆ ≤ Z₀ := marked_mixed_commutator_le s t
    (by simpa only [← hP] using hPA)
    (hAlocal.trans (hatV_normalized R _ _)) hAA hFA
    (sup_le hKA hWA) (sup_le le_sup_left hWC) hCC
    ((commutator_mono le_rfl hAQ).trans hWQ) (by simpa only [hP] using hAP)
  have hAK : ⁅A,K⁆ ≤ Z₀ := (commutator_mono le_rfl le_sup_left).trans hAB
  have hAC : ⁅A,C⁆ ≤ Z₀ := by
    rw [← commutator_eq_of_centralizing_sup
      (show Z₀ ⊔ K = C from sup_comm _ _) hZAc (hKA.trans A.le_normalizer)]
    exact hAK
  have hderived : ⁅⁅A,A⁆,P⁆ ≤ Z₀ := by
    apply commutator_commutator_le_of_rotate_of_le_normalizer
      (hAlocal.trans hPZ) (hAlocal.trans hPZ) hPZ
    · exact (commutator_mono hAP (le_refl A)).trans
        ((commutator_comm C A).trans_le hAC)
    · rw [commutator_comm P A]
      exact (commutator_mono hAP (le_refl A)).trans
        ((commutator_comm C A).trans_le hAC)
  have hFP : ⁅F,P⁆ ≤ Z₀ := by
    let D := commutatorPreimage P P Z₀
    have hFD : F ≤ D := by
      change hatV R (alpha R) (p.walk.getVert 6) ≤ D
      rw [← (Higher.OrbitGeometry.Source.commutator_layers common earlier p).2]
      apply sup_le
      · exact le_commutatorPreimage
          ((le_normalizer_iff_commutator_le_left.mp A.le_normalizer).trans hAlocal) hderived
      · exact le_commutatorPreimage (Z_le_stabilizer R _)
          (le_normalizer_iff_commutator_le_left.mp hPZ)
    exact (commutator_mono hFD le_rfl).trans (commutator_commutatorPreimage_le P P Z₀ hPZ)
  exact marked_dual_nontrivial s (by simpa only [hP] using hFP)

/-- The first dual layer occurs in the actual core derived subgroup modulo Z. -/
theorem first_le_core_derived_sup_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    hatV R (alpha R) (p.walk.getVert 6) ≤
      ⁅core R (alpha R),core R (alpha R)⁆ ⊔ Z R (alpha R) := by
  obtain ⟨s⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  have hKA := Early.Orbit.Source.Complete.core_le_third_hat common earlier p
  have hD : ⁅core R (alpha R),core R (alpha R)⁆ ≤
      hatV R (alpha R) (p.walk.getVert 6) :=
    (commutator_mono hKA hKA).trans
      (le_sup_left.trans (Higher.OrbitGeometry.Source.commutator_layers common earlier p).2.le)
  have hn : Mbar R ≤ normalizer (⁅core R (alpha R),core R (alpha R)⁆ : Subgroup (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (HomSaturation.core_normalized hg)]
  exact (s.sup_eq_of_not_le hD hn (core_derived_not_le_Z common earlier p)).ge

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
