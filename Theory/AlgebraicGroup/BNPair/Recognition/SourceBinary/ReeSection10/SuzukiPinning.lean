module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FixedKernel
public import Theory.SpecificGroups.Suzuki.BorelPairGeometry
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRankOne

/-!
# Pinning the literal Suzuki reflection, including Sz(2)

The root-regular ovoid action identifies the complete Borel with the infinity
stabilizer for every parameter. An outside element whose square lies in that
Borel exchanges two points. Moving those points to infinity and zero writes
it as torus times Weyl and proves its square is one. Taking a square root in
the odd torus then aligns it with the standard Weyl matrix by a Borel
conjugation. The binary case uses its trivial torus explicitly.

The source application applies this calculation to the actual marked endpoint
projection. It proves the square of the given N-lift, and changes the entire
Suzuki marking by a Borel conjugator while preserving its full root normalizer.
No opposite-root or coordinate equation is assumed as part of the marking.

Source: Fong--Seitz II (1974), pp.221--222, the natural basis (10.4);
Huppert--Blackburn III, XI.3.3 and XI.3.10. The Borel-conjugator argument extends
`Theory.SpecificGroups.Suzuki.BorelPairGeometry` to the binary parameter.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

private theorem root_fixes_infinity (m : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) :
    g • suzukiOvoidInfinity m = suzukiOvoidInfinity m := by
  obtain ⟨a,b,hg⟩ := (mem_suzukiRootSubgroup_iff m g).mp hg
  apply Subtype.ext
  change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv • _ = _
  rw [hg]
  dsimp only [suzukiOvoidInfinity]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]

private theorem borel_le_stabilizer (m : ℕ) :
    SuzukiBorelSubgroup m ≤ MulAction.stabilizer (SuzukiMatrixGroup m)
      (suzukiOvoidInfinity m) := by
  rw [suzukiBorelSubgroup_eq_sup]
  apply sup_le
  · intro g hg
    exact root_fixes_infinity m g hg
  · intro g hg
    obtain ⟨a,ha⟩ := (mem_suzukiSplitTorus_iff m g).mp hg
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv • _ = _
    rw [ha]
    exact External.suzukiTorus_smul_infinity m a

/-- The matrix Borel is the infinity stabilizer, also for Sz(2). -/
theorem suzuki_borel_stabilizer (m : ℕ) :
    SuzukiBorelSubgroup m = MulAction.stabilizer (SuzukiMatrixGroup m)
      (suzukiOvoidInfinity m) := by
  apply le_antisymm (borel_le_stabilizer m)
  intro g hg
  rcases External.suzukiMatrixGroup_bruhat_decomposition m (suzukiTits m)
    (suzukiTits_sq m) (suzukiTits_apply m) g.val g.property with hB | ⟨b,f,hb,hf,he⟩
  · exact hB
  · have hbG : b ∈ SuzukiMatrixSubgroup m :=
      (sup_le (suzukiRootClosure_le m) (suzukiSplitTorusClosure_le m)) hb
    have hfG : f ∈ SuzukiMatrixSubgroup m := suzukiRootClosure_le m hf
    let b' : SuzukiMatrixGroup m := ⟨b,hbG⟩
    let f' : SuzukiMatrixGroup m := ⟨f,hfG⟩
    have hb' : b' • suzukiOvoidInfinity m = suzukiOvoidInfinity m :=
      borel_le_stabilizer m hb
    have hf' : f' • suzukiOvoidInfinity m = suzukiOvoidInfinity m :=
      root_fixes_infinity m f' hf
    have he' : g = b' * suzukiWeyl m * f' := Subtype.ext he
    change g • suzukiOvoidInfinity m = suzukiOvoidInfinity m at hg
    rw [he',mul_smul,mul_smul,hf',suzukiWeyl_smul_infinity] at hg
    exact ((suzukiOvoidInfinity_ne_zero m)
      ((MulAction.injective b') (hb'.trans hg.symm))).elim

/-- An element outside the Borel whose square is in the Borel is an
involution. Root regularity sends its two exchanged points to infinity and
zero, where the calculation is torus times Weyl. -/
theorem suzuki_square_borel (m : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∉ SuzukiBorelSubgroup m) (hgg : g*g ∈ SuzukiBorelSubgroup m) :
    g*g = 1 := by
  have hgi : g • suzukiOvoidInfinity m ≠ suzukiOvoidInfinity m := by
    simpa only [suzuki_borel_stabilizer, MulAction.mem_stabilizer_iff] using hg
  obtain ⟨r,hr,_⟩ := suzukiRootSubgroup_regular m (g • suzukiOvoidInfinity m)
    (suzukiOvoidZero m) hgi (suzukiOvoidInfinity_ne_zero m).symm
  have hri := root_fixes_infinity m (r : SuzukiMatrixGroup m) r.property
  have hrii := root_fixes_infinity m (r : SuzukiMatrixGroup m)⁻¹
    ((SuzukiRootSubgroup m).inv_mem r.property)
  let y := MulAut.conj (r : SuzukiMatrixGroup m) g
  have hyi : y • suzukiOvoidInfinity m = suzukiOvoidZero m := by
    simpa only [y,MulAut.conj_apply,mul_smul,hrii] using hr
  have hyz : y • suzukiOvoidZero m = suzukiOvoidInfinity m := by
    rw [←hyi,←mul_smul]
    have he : y*y = MulAut.conj (r : SuzukiMatrixGroup m) (g*g) :=
      (map_mul _ _ _).symm
    rw [he,MulAut.conj_apply,mul_smul,mul_smul,hrii,
      show (g*g) • suzukiOvoidInfinity m = suzukiOvoidInfinity m from
        borel_le_stabilizer m hgg,hri]
  let t : SuzukiSplitTorus m := ⟨y * suzukiWeyl m, by
    rw [mem_suzukiSplitTorus_iff_fix_pair]
    simp only [mul_smul,suzukiWeyl_smul_infinity,suzukiWeyl_smul_zero,hyi,hyz,and_self]⟩
  have hyy : y*y = 1 := by
    have he : y = (t : SuzukiMatrixGroup m) * suzukiWeyl m := by
      simp [t,mul_assoc,suzukiWeyl_sq]
    rw [he]
    calc
      _ = (t : SuzukiMatrixGroup m) *
          (suzukiWeyl m * t * suzukiWeyl m) := by group
      _ = 1 := by rw [suzukiWeyl_conj_splitTorus,mul_inv_cancel]
  apply (MulAut.conj (r : SuzukiMatrixGroup m)).injective
  simpa only [map_mul,map_one] using hyy


/-- Full root normalizer, with no positive-parameter restriction. -/
theorem suzuki_root_normalizer (m : ℕ) :
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) = SuzukiBorelSubgroup m := by
  apply le_antisymm
  · intro g hg
    have hn : Nontrivial (SuzukiRootSubgroup m) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.matrixRoot_card]
      have hq : 1 < 2 ^ (2*m+1) := one_lt_pow₀ (by decide) (by omega)
      nlinarith
    obtain ⟨r,hr⟩ := exists_ne (1 : SuzukiRootSubgroup m)
    have hmem : g⁻¹ * (r : SuzukiMatrixGroup m) * g ∈ SuzukiRootSubgroup m :=
      (mem_normalizer_iff''.mp hg _).mp r.property
    have hfix : (r : SuzukiMatrixGroup m) • (g • suzukiOvoidInfinity m) =
        g • suzukiOvoidInfinity m := by
      have h := congrArg (g • ·) (root_fixes_infinity m _ hmem)
      simpa only [mul_smul, smul_inv_smul] using h
    rw [suzuki_borel_stabilizer, MulAction.mem_stabilizer_iff]
    by_contra hgi
    obtain ⟨u,_,hu⟩ := suzukiRootSubgroup_regular m
      (g • suzukiOvoidInfinity m) (g • suzukiOvoidInfinity m) hgi hgi
    exact hr ((hu r hfix).trans (hu 1 (one_smul _ _)).symm)
  · rw [suzukiBorelSubgroup_eq_sup]
    exact sup_le le_normalizer (suzukiSplitTorus_le_normalizer_root m)

private theorem splitTorus_odd (m : ℕ) : Odd (Nat.card (SuzukiSplitTorus m)) := by
  by_cases hm : m = 0
  · subst m
    have hu : Subsingleton (BinaryGaloisField 1)ˣ := by
      apply (Nat.card_eq_one_iff_unique.mp ?_).1
      rw [Nat.card_units, GaloisField.card 2 1 (by decide)]
      norm_num
    have ht : Subsingleton (SuzukiSplitTorus 0) := by
      apply subsingleton_of_forall_eq 1
      intro t
      obtain ⟨a,ha⟩ := (mem_suzukiSplitTorus_iff 0 t).mp t.property
      have ha1 : a = 1 := @Subsingleton.elim _ hu _ _
      apply Subtype.ext
      apply Subtype.ext
      rw [ha,ha1]
      exact External.suzukiTorusGL_one 0
    rw [Nat.card_eq_one_iff_unique.mpr ⟨ht,⟨1⟩⟩]
    exact odd_one
  · rw [suzukiSplitTorus_card m (by omega)]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (by omega)) odd_one

/-- A Borel conjugator aligns any outside involution with the standard Weyl
matrix, including the cyclic-root case Sz(2). -/
theorem suzuki_borel_conj_weyl (m : ℕ)
    (u : SuzukiMatrixGroup m) (hu : IsInvolution u) (huB : u ∉ SuzukiBorelSubgroup m) :
    ∃ b ∈ SuzukiBorelSubgroup m, MulAut.conj b (suzukiWeyl m) = u := by
  have hui : u • suzukiOvoidInfinity m ≠ suzukiOvoidInfinity m := by
    simpa only [suzuki_borel_stabilizer m, MulAction.mem_stabilizer_iff] using huB
  obtain ⟨r, hr, _⟩ := suzukiRootSubgroup_regular m (u • suzukiOvoidInfinity m)
    (suzukiOvoidZero m) hui (suzukiOvoidInfinity_ne_zero m).symm
  have hrii := root_fixes_infinity m _
    ((SuzukiRootSubgroup m).inv_mem r.property)
  let y := MulAut.conj (r : SuzukiMatrixGroup m) u
  have hyi : y • suzukiOvoidInfinity m = suzukiOvoidZero m := by
    simpa only [y, MulAut.conj_apply, mul_smul, hrii] using hr
  have hyy : y * y = 1 := by
    rw [← pow_two, ← map_pow, hu.2, map_one]
  have hyz : y • suzukiOvoidZero m = suzukiOvoidInfinity m := by
    rw [← hyi, ← mul_smul, hyy, one_smul]
  have hyt : y * suzukiWeyl m ∈ SuzukiSplitTorus m := by
    rw [mem_suzukiSplitTorus_iff_fix_pair]
    simp only [mul_smul, suzukiWeyl_smul_infinity, suzukiWeyl_smul_zero, hyi, hyz, and_self]
  let t : SuzukiSplitTorus m := ⟨y * suzukiWeyl m, hyt⟩
  have hodd := splitTorus_odd m
  obtain ⟨s, hs⟩ := (Nat.coprime_two_right.mpr hodd).pow_left_bijective.surjective t
  have hconj : MulAut.conj (s : SuzukiMatrixGroup m) (suzukiWeyl m) = y := by
    have hinv := suzukiWeyl_conj_splitTorus m s⁻¹
    change suzukiWeyl m * (s : SuzukiMatrixGroup m)⁻¹ * suzukiWeyl m =
      ((s : SuzukiMatrixGroup m)⁻¹)⁻¹ at hinv
    rw [inv_inv] at hinv
    have hs' : (s : SuzukiMatrixGroup m) * s = y * suzukiWeyl m := by
      simpa only [pow_two, Subgroup.coe_mul, t] using congrArg Subtype.val hs
    change (s : SuzukiMatrixGroup m) * suzukiWeyl m * (s : SuzukiMatrixGroup m)⁻¹ = y
    calc
      _ = s * (suzukiWeyl m * (s : SuzukiMatrixGroup m)⁻¹ * suzukiWeyl m) *
          suzukiWeyl m := by rw [mul_assoc, mul_assoc, mul_assoc, suzukiWeyl_sq, mul_one]
      _ = (s : SuzukiMatrixGroup m) * s * suzukiWeyl m := by rw [hinv]
      _ = y := by rw [hs', mul_assoc, suzukiWeyl_sq, mul_one]
  refine ⟨(r : SuzukiMatrixGroup m)⁻¹ * s,
    (SuzukiBorelSubgroup m).mul_mem
      ((SuzukiBorelSubgroup m).inv_mem ((show SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m by
        rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_left) r.property))
      ((show SuzukiSplitTorus m ≤ SuzukiBorelSubgroup m by
        rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_right) s.property), ?_⟩
  calc
    _ = (r : SuzukiMatrixGroup m)⁻¹ *
        (MulAut.conj (s : SuzukiMatrixGroup m) (suzukiWeyl m)) * r := by
      simp only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]
    _ = u := by rw [hconj]; simp [y, MulAut.conj_apply, mul_assoc]

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace SuzukiPinning
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (s : ReeSource.RootReflection Q split i)

/-- The given reflection under the literal endpoint projection. -/
def reflectionMatrix : SuzukiMatrixGroup m :=
  suzukiActorEquiv Q split i m μ hB ⟨s.val,s.mem_rankOne⟩

theorem reflectionMatrix_not_borel : reflectionMatrix Q split i m μ hB s ∉
    SuzukiBorelSubgroup m := by
  intro hs
  have hB' : (quotientBorel Q i).map μ.toMonoidHom = SuzukiBorelSubgroup m :=
    hB.trans (suzuki_root_normalizer m)
  rw [←hB',mem_map_equiv] at hs
  apply rootReflectionProjection_not_mem_borel Q split i s
  have he : inclusion (rankOne_le_parabolic Q split i) ⟨s.val,s.mem_rankOne⟩ =
      rootReflectionEndpoint Q split i s := Subtype.ext rfl
  simpa only [reflectionMatrix,suzukiActorEquiv_apply,he,MulEquiv.symm_apply_apply] using hs

theorem reflectionMatrix_square_borel :
    reflectionMatrix Q split i m μ hB s * reflectionMatrix Q split i m μ hB s ∈
      SuzukiBorelSubgroup m := by
  have hq : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      (s.val*s.val) = 1 := by
    rw [map_mul,s.class_eq]
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
  have hh : ((s.val*s.val : Q.tits.N) : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N :=
    (QuotientGroup.eq_one_iff (s.val*s.val)).mp hq
  rw [←suzuki_root_normalizer,←hB]
  change μ (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s)) *
    μ (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s)) ∈ _
  rw [←map_mul,←map_mul]
  apply mem_map_of_mem
  apply mem_map_of_mem
  exact hh.1

include μ hB in
/-- The literal given source reflection, without altering its lift, is an involution. -/
theorem reflection_square : (s.val : X ⧸ Q.D) * s.val = 1 := by
  have he := suzuki_square_borel m (reflectionMatrix Q split i m μ hB s)
    (reflectionMatrix_not_borel Q split i m μ hB s)
    (reflectionMatrix_square_borel Q split i m μ hB s)
  have hr : (⟨s.val,s.mem_rankOne⟩ : rankOne Q split i) * ⟨s.val,s.mem_rankOne⟩ = 1 := by
    apply (suzukiActorEquiv Q split i m μ hB).injective
    simpa only [map_mul,map_one,reflectionMatrix] using he
  exact congrArg Subtype.val hr

/-- The Borel change of basis preserves the complete rank-one marking. -/
theorem exists_alignment : ∃ b ∈ SuzukiBorelSubgroup m,
    MulAut.conj b (suzukiWeyl m) = reflectionMatrix Q split i m μ hB s := by
  apply suzuki_borel_conj_weyl
  · exact ⟨fun he => reflectionMatrix_not_borel Q split i m μ hB s
      (he ▸ (SuzukiBorelSubgroup m).one_mem),by
        simpa only [pow_two] using suzuki_square_borel m _
          (reflectionMatrix_not_borel Q split i m μ hB s)
          (reflectionMatrix_square_borel Q split i m μ hB s)⟩
  · exact reflectionMatrix_not_borel Q split i m μ hB s

def alignmentMatrix : SuzukiMatrixGroup m :=
  (exists_alignment Q split i m μ hB s).choose

theorem alignmentMatrix_mem : alignmentMatrix Q split i m μ hB s ∈ SuzukiBorelSubgroup m :=
  (exists_alignment Q split i m μ hB s).choose_spec.1

def alignedModel : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m :=
  μ.trans (MulAut.conj (alignmentMatrix Q split i m μ hB s)⁻¹)

theorem alignedModel_borel : (quotientBorel Q i).map
    (alignedModel Q split i m μ hB s).toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) := by
  change (quotientBorel Q i).map ((MulAut.conj
    (alignmentMatrix Q split i m μ hB s)⁻¹).toMonoidHom.comp μ.toMonoidHom) = _
  rw [←map_map,hB,suzuki_root_normalizer]
  let b := alignmentMatrix Q split i m μ hB s
  have hb : b ∈ SuzukiBorelSubgroup m := alignmentMatrix_mem Q split i m μ hB s
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact (SuzukiBorelSubgroup m).mul_mem
      ((SuzukiBorelSubgroup m).mul_mem ((SuzukiBorelSubgroup m).inv_mem hb) hy)
      ((SuzukiBorelSubgroup m).inv_mem ((SuzukiBorelSubgroup m).inv_mem hb))
  · intro x hx
    refine ⟨b*x*b⁻¹,(SuzukiBorelSubgroup m).mul_mem
      ((SuzukiBorelSubgroup m).mul_mem hb hx) ((SuzukiBorelSubgroup m).inv_mem hb),?_⟩
    change b⁻¹*(b*x*b⁻¹)*b = x
    group

theorem alignedModel_reflection :
    suzukiActorEquiv Q split i m (alignedModel Q split i m μ hB s)
      (alignedModel_borel Q split i m μ hB s) ⟨s.val,s.mem_rankOne⟩ = suzukiWeyl m := by
  change MulAut.conj (alignmentMatrix Q split i m μ hB s)⁻¹
    (reflectionMatrix Q split i m μ hB s) = _
  rw [←(exists_alignment Q split i m μ hB s).choose_spec.2]
  simp [alignmentMatrix,MulAut.conj_apply,mul_assoc]

end SuzukiPinning
end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
