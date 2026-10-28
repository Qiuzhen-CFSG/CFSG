module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment.Transfer

/-!
# Single commutators detect the original G₂ covering center

Every vector in the upper three-space preimage outside the scalar radical is
one displacement by the full A-B-C actor. Explicit root coordinates retain
the scalar entry; solving the four displacement equations proves the claim.
The universal cover map transports it to the original module. Conversely,
exact fixed-vector lifting shows that a single inner displacement in the
covering center is zero. The last theorem gives this test on the literal
conjugate module, for the reciprocal actor used in CenterComparison.Reciprocal.

Source: Aschbacher--Smith B.4.6(7) and the central-cover repair of 11.2.2(5),
printed pp.88,768. Coordinates use the existing attributed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion Atlas.G2.Explicit
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

private def lowerVector (r s t : F) : TraceZero F :=
  ⟨![0,0,0,0,0,r,s,t],by simp [trace]⟩

private theorem displacement (a b c r s t : F) :
    (RootCentralizers.coverAction F (rootA a * rootB b * rootC c)
      (lowerVector F r s t) - lowerVector F r s t).val =
        ![a*s+b*r+c^2*t,a*t+c*r,b*t+c*s,c*t,c*t,0,0,0] := by
  ext i
  fin_cases i <;> simp [RootCentralizers.coverAction,restrictScalars,traceZeroAction_val,
    rootA,rootB,rootC,rootAEquiv,rootBEquiv,rootCEquiv,rootALinear,rootBLinear,rootCLinear,
    rootAApply,rootBApply,rootCApply,lowerVector,sub_eq_add_neg,CharTwo.neg_eq,CharTwo.add_self_eq_zero] <;> ring

omit [Algebra (ZMod 2) F] in
private theorem exists_parameters (x y z d : F) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    ∃ a b c r s t : F,
      a*s+b*r+c^2*t=x ∧ a*t+c*r=y ∧ b*t+c*s=z ∧ c*t=d := by
  by_cases hy : y = 0
  · by_cases hz : z = 0
    · have hx : x ≠ 0 := hne.resolve_right (by simp [hy,hz])
      by_cases hd : d = 0
      · exact ⟨1,0,0,0,x,0,by simp [hy,hz,hd]⟩
      · refine ⟨0,0,x/d,0,0,d^2/x,?_,?_,?_,?_⟩
        · field_simp; ring
        · simp [hy]
        · simp [hz]
        · field_simp
    · refine ⟨d*((x+d^2)/z),z,d,(x+d^2)/z,0,1,?_,?_,?_,?_⟩
      · field_simp
        simp [_root_.add_mul,add_assoc,CharTwo.add_self_eq_zero]
      · simp [hy,CharTwo.add_self_eq_zero]
      · simp
      · simp
  · refine ⟨y,z+d*((x+d^2)/y),d,0,(x+d^2)/y,1,?_,?_,?_,?_⟩
    · field_simp
      simp [_root_.mul_add,add_assoc,CharTwo.add_self_eq_zero]
    · simp
    · simp [add_assoc,CharTwo.add_self_eq_zero]
    · simp

/-- Every noncentral vector in the full upper preimage is one displacement,
not merely a sum of displacements. The scalar coordinate is retained. -/
theorem exists_displacement (x : TraceZero F)
    (hx : x ∈ RootCentralizers.threePreimage F)
    (hne : x ∉ scalarLine F) :
    ∃ b ∈ EvenTwoRank.elementary F, ∃ y : TraceZero F,
      RootCentralizers.coverAction F b y-y=x := by
  have h5 : x.val 5 = 0 := hx.1
  have h6 : x.val 6 = 0 := hx.2.1
  have h7 : x.val 7 = 0 := hx.2.2
  have h4 : x.val 4 = x.val 3 := by
    have hh : x.val 3+x.val 4=0 := x.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hh
  have hn : x.val 0 ≠ 0 ∨ x.val 1 ≠ 0 ∨ x.val 2 ≠ 0 := by
    by_contra! hn
    apply hne
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x.val 3,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [identity,unit,h4,h5,h6,h7,hn.1,hn.2.1,hn.2.2]
  obtain ⟨a,b,c,r,s,t,h0,h1,h2,h3⟩ := exists_parameters F _ _ _ (x.val 3) hn
  refine ⟨rootA a*rootB b*rootC c,
    (EvenTwoRank.elementary F).mul_mem
      ((EvenTwoRank.elementary F).mul_mem
        (NaturalOffenders.rootA_mem_elementary a) (NaturalOffenders.rootB_mem_elementary b))
      (NaturalOffenders.rootC_mem_elementary c),lowerVector F r s t,?_⟩
  apply Subtype.ext
  rw [displacement]
  ext i
  fin_cases i <;> simp [h0,h1,h2,h3,h4,h5,h6,h7]
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))

/-- An inner G₂ displacement cannot be a nonzero covering-central vector. -/
theorem displacement_central_eq_zero (b : Model S.field.Carrier) (v : D.space)
    (h : Preliminary.markedAction D m b v-v ∈ Preliminary.centralSpace D) :
    Preliminary.markedAction D m b v-v=0 := by
  have hk : Preliminary.markedProjection D m
      (Preliminary.markedAction D m b v-v)=0 := by
    change _ ∈ (Preliminary.markedProjection D m).toLinearMap.ker
    rwa [Preliminary.markedProjection_ker]
  have he := LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' b) v
  have hv : (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)) b
      (Preliminary.markedProjection D m v) = Preliminary.markedProjection D m v := by
    rw [map_sub,sub_eq_zero] at hk
    exact he.symm.trans hk
  have hf : v ∈ fixedSpace (Preliminary.markedAction D m) (zpowers b) := by
    rw [marked_fixedSpace]
    exact (mem_fixedSpace_zpowers_iff _ _ _).mpr hv
  exact sub_eq_zero.mpr ((mem_fixedSpace_zpowers_iff _ _ _).mp hf)


private theorem original_displacement (v : D.space)
    (hv : Preliminary.markedAction D m (rootC 1) v=v)
    (hne : v ∉ Preliminary.centralSpace D) :
    ∃ b ∈ EvenTwoRank.elementary S.field.Carrier, ∃ w : D.space,
      Preliminary.markedAction D m b w-w=v := by
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1<2) S.nonbinary
  obtain ⟨p,hp,hover⟩ := OrthogonalCover.ParabolicFixed.exists_full_quotient
    S.field.Carrier (Preliminary.markedProjection D m) hq
    (Preliminary.markedProjection_isCover D m)
  obtain ⟨x,hx⟩ := hp v
  have hf : Natural.action S.field.Carrier (rootC 1) (mk S.field.Carrier x) =
      mk S.field.Carrier x := by
    rw [←hover,hx]
    have hh := LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' (rootC 1)) v
    change Preliminary.markedProjection D m (Preliminary.markedAction D m (rootC 1) v) =
      Natural.action S.field.Carrier (rootC 1) (Preliminary.markedProjection D m v) at hh
    rw [hv] at hh
    exact hh.symm
  have hfix := Extensions.traceZero_fixed_of_natural_fixed (rootC 1) x hf
  have h5 : x.val 5=0 := by
    have hh := congrArg (fun y : TraceZero S.field.Carrier => y.val 1) hfix
    simpa [traceZeroAction_val,rootC,rootCEquiv,rootCLinear,rootCApply] using hh
  have h6 : x.val 6=0 := by
    have hh := congrArg (fun y : TraceZero S.field.Carrier => y.val 2) hfix
    simpa [traceZeroAction_val,rootC,rootCEquiv,rootCLinear,rootCApply] using hh
  have h7 : x.val 7=0 := by
    have hh := congrArg (fun y : TraceZero S.field.Carrier => y.val 4) hfix
    simpa [traceZeroAction_val,rootC,rootCEquiv,rootCLinear,rootCApply] using hh
  have hn : x ∉ scalarLine S.field.Carrier := by
    intro hscalar
    apply hne
    rw [←Preliminary.markedProjection_ker D m]
    change Preliminary.markedProjection D m v=0
    rw [←hx,hover]
    exact Submodule.Quotient.mk_eq_zero _ |>.mpr hscalar
  obtain ⟨b,hb,y,hy⟩ := exists_displacement S.field.Carrier x ⟨h5,h6,h7⟩ hn
  refine ⟨b,hb,p y,?_⟩
  have he := LinearMap.congr_fun (p.isIntertwining' b) y
  change p (RootCentralizers.coverAction S.field.Carrier b y) =
    Preliminary.markedAction D m b (p y) at he
  rw [←he,←map_sub,hy,hx]

/-- The center is the only obstruction to writing a fixed vector as one
literal commutator on the original full module. -/
theorem fixed_noncentral_is_commutator (A : Subgroup G)
    (a : A →* Model S.field.Carrier)
    (hact : ∀ (x : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G)*(D.spaceEquiv (Multiplicative.ofAdd v) : G)*(x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (x : G) (hx : x ∈ V ⊓ centralizer (A : Set G))
    (hne : x ∉ V ⊓ centralizer (L : Set G)) :
    ∃ b ∈ A, ∃ y ∈ V, ⁅b,y⁆=x := by
  let v : D.space := (D.spaceEquiv.symm ⟨x,hx.1⟩).toAdd
  have hvx : (D.spaceEquiv (Multiplicative.ofAdd v) : G)=x := by
    simp only [v,ofAdd_toAdd,MulEquiv.apply_symm_apply]
  have hv : Preliminary.markedAction D m (rootC 1) v=v := by
    obtain ⟨b,hb⟩ := ha.symm ▸ NaturalOffenders.rootC_mem_elementary (1:S.field.Carrier)
    apply D.spaceEquiv.injective
    apply Subtype.ext
    change (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (rootC 1) v)) : G)=
        (D.spaceEquiv (Multiplicative.ofAdd v) : G)
    rw [←hb,hact,hvx]
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 b b.property)
  have hn : v ∉ Preliminary.centralSpace D := by
    intro h
    exact hne ⟨hx.1,hvx ▸ (Preliminary.mem_centralSpace_iff D v).mp h⟩
  obtain ⟨b,hb,w,hw⟩ := original_displacement D S m v hv hn
  obtain ⟨z,hz⟩ := ha.symm ▸ hb
  refine ⟨z,z.property,D.spaceEquiv (Multiplicative.ofAdd w),
    (D.spaceEquiv (Multiplicative.ofAdd w)).property,?_⟩
  have he := congrArg (fun t : D.space =>
    (D.spaceEquiv (Multiplicative.ofAdd t) : G)) hw
  rw [ofAdd_sub,map_div,Subgroup.coe_div,div_eq_mul_inv,←hz,hact,hvx] at he
  exact he

/-- No single inner commutator on the reciprocal module is a nonzero
vector in its full covering center. -/
theorem reciprocal_central_commutator_eq_one (g : G) (B : Subgroup G)
    (b : B →* Model S.field.Carrier)
    (hact : ∀ (x : B) (v : D.space),
      MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd
        (Preliminary.markedAction D m (b x) v)) : G) =
        (x : G)*MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd v) : G)*(x : G)⁻¹)
    (x : B) (y : G) (hy : y ∈ V.map (MulAut.conj g).toMonoidHom)
    (hc : ⁅(x:G),y⁆ ∈ (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom) :
    ⁅(x:G),y⁆=1 := by
  obtain ⟨z,hz,rfl⟩ := hy
  let v : D.space := (D.spaceEquiv.symm ⟨z,hz⟩).toAdd
  let j : Multiplicative D.space →* G :=
    (MulAut.conj g).toMonoidHom.comp (V.subtype.comp D.spaceEquiv.toMonoidHom)
  have hv : (D.spaceEquiv (Multiplicative.ofAdd v) : G)=z := by
    simp only [v,ofAdd_toAdd,MulEquiv.apply_symm_apply]
  have he : j (Multiplicative.ofAdd (Preliminary.markedAction D m (b x) v-v)) =
      ⁅(x:G),MulAut.conj g z⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv]
    change MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (b x) v)) : G) *
      (MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd v) : G))⁻¹ = _
    rw [hact,hv]
    rfl
  have hd : Preliminary.markedAction D m (b x) v-v ∈ Preliminary.centralSpace D := by
    apply (Preliminary.mem_centralSpace_iff D _).mpr
    have hh := he.symm ▸ hc
    obtain ⟨c,hc,heq⟩ := hh
    have hc' := (MulAut.conj g).injective heq
    change c = (D.spaceEquiv (Multiplicative.ofAdd _):G) at hc'
    rw [←hc']
    exact hc.2
  have hh := displacement_central_eq_zero D S m (b x) v hd
  rw [hh,ofAdd_zero,map_one] at he
  exact he.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison
