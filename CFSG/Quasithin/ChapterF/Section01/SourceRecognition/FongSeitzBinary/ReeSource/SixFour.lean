module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveSixFourFactor
public import Theory.Frattini.Intersection
public import Theory.Frattini.SquareImage

/-!
# The Frattini argument completing source (6.4)

Write V = U ∩ U^s₂. Every shifted Suzuki Omega root contained in V lies
in Φ(V), including when its parameter is zero. The whole parabolic normalizes
Φ(V). A natural linear panel gives an exponent-two image of U; its map
therefore kills Φ(U). Conjugating by s₂ shows that Φ(V) meets U₁^s₂
trivially.

The preceding two-factor support bound places [U₂,U₁^(s₂s₁s₂)] in
Omega₁(U₂^(s₁s₂)) U₁^s₂. Reflect its elements by s₁s₂s₁ into [V,V].
A nonidentity linear component would then meet Φ(V) in the other linear
root. The actual Cartan action fills that root (also over F₂), so the
original commutator lies in Φ(V). Its linear component consequently lies
in the forbidden intersection. This removes the linear factor and finishes
both assertions of (6.4), using the already proved Omega centralization.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, (6.4).
The two field orders remain independent in the main theorem. The
common-field specialization retains the earlier odd-linear-degree premise;
neither pairing nor odd degree is asserted here. OriginalSixFour applies
the result to both original endpoint maps and the literal quotient Q.q.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include μ hB in
theorem source_omega_le_frattini (w : Weyl Q)
    (hA : rootAt Q split i w ≤ simpleRemainder Q split i) :
    omegaOneAmbient (rootAt Q split i w) ≤
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split i).map e.toMonoidHom = rootAt Q split i w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hΩ : omegaOneAmbient (rootAt Q split i w) =
      (frattini (rootAt Q split i w)).map (rootAt Q split i w).subtype := by
    rw [← he,frattini_image_map _ _ e.injective,
      suzuki_frattini_image Q split i m μ hB,
      map_omegaOneAmbient_injective e.toMonoidHom e.injective]
  rw [hΩ]
  exact frattini_image_le_of_le hA (split.isTwo.to_le inf_le_left)

include μ hB in
theorem source_frattini_parabolic_normalizes :
    Endpoint Q i ≤ normalizer
      (((frattini (simpleRemainder Q split i)).map
        (simpleRemainder Q split i).subtype : Subgroup (X ⧸ Q.D)) : Set _) :=
  (remainder_parabolic_normalizes Q split i
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)).trans
      (normalizer_le_normalizer_characteristic_image _ _)

include ν hC in
private theorem linear_square (a : simpleRoot Q split j) : a^2 = 1 := by
  apply (linearRootEquiv Q split j ν T hC).injective
  rw [map_pow,map_one]
  apply Multiplicative.toAdd.injective
  change 2 • (linearRootEquiv Q split j ν T hC a).toAdd = 0
  exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)

include ν hC in
private theorem unipotent_frattini_le_linear_kernel :
    (frattini split.U).map split.U.subtype ≤ embeddedPanelKernel Q j := by
  let f : split.U →* (Endpoint Q j ⧸ panelKernel Q j) :=
    (QuotientGroup.mk' (panelKernel Q j)).comp
      (inclusion (split.U_le.trans (Q.tits.B_le_standardParabolic _)))
  have hsq (u : split.U) : f u ^ 2 = 1 := by
    have hp : (u : X ⧸ Q.D) ∈
        (simpleRoot Q split j : Set (X ⧸ Q.D)) * (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]; exact u.property
    obtain ⟨a,ha,b,hb,hab⟩ := hp
    have hk := remainder_le_panelKernel_of_marking Q split j ν T hC
      (linear_normalizer_index T) hb
    have hbP : b ∈ Endpoint Q j := Q.tits.B_le_standardParabolic _ (split.U_le hb.1)
    have hbK : (⟨b,hbP⟩ : Endpoint Q j) ∈ panelKernel Q j := by
      obtain ⟨v,hv,he⟩ := hk
      exact (Subtype.ext he : v = ⟨b,hbP⟩) ▸ hv
    have hf : f u = rootProjection Q split j ⟨a,ha⟩ := by
      have hu : (⟨u,split.U_le.trans (Q.tits.B_le_standardParabolic _) u.property⟩ : Endpoint Q j) =
          rootInEndpoint Q split j ⟨a,ha⟩ * ⟨b,hbP⟩ := Subtype.ext hab.symm
      change QuotientGroup.mk' (panelKernel Q j)
        (⟨u,split.U_le.trans (Q.tits.B_le_standardParabolic _) u.property⟩ : Endpoint Q j) = _
      have hbq : QuotientGroup.mk' (panelKernel Q j) ⟨b,hbP⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hbK
      rw [hu,map_mul,hbq,mul_one]
      rfl
    rw [hf,←map_pow,linear_square Q split j ν T hC,map_one]
  rintro x ⟨u,hu,rfl⟩
  have hk := Theory.GroupTheory.frattini_le_ker_of_square_image f hsq hu
  exact mem_map_of_mem (Endpoint Q j).subtype ((QuotientGroup.eq_one_iff _).mp hk)

include μ hB ν hC in
theorem source_frattini_disjoint_first_linear :
    Disjoint (rootAt Q split j (Q.simple i))
      ((frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype) := by
  let D := (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype
  let s := reflectionLift Q i
  have hn : (s : X ⧸ Q.D) ∈ normalizer (D : Set _) :=
    source_frattini_parabolic_normalizes Q split i m μ hB s.property
  have hDK : D ≤ embeddedPanelKernel Q j :=
    (frattini_image_le_of_le (show simpleRemainder Q split i ≤ split.U from inf_le_left)
      split.isTwo).trans (unipotent_frattini_le_linear_kernel Q split j ν T hC)
  apply disjoint_def.mpr
  intro x hx hd
  have hxA : (s : X ⧸ Q.D)*x*(s : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j := hx
  have hxD : (s : X ⧸ Q.D)*x*(s : X ⧸ Q.D)⁻¹ ∈ D :=
    (mem_normalizer_iff.mp hn x).mp hd
  have he := disjoint_def.mp (simpleRoot_disjoint_panelKernel Q split j) hxA (hDK hxD)
  exact (MulAut.conj (s : X ⧸ Q.D)).injective (he.trans (map_one _).symm)

omit F [Field F] [Finite F] [CharP F 2] ν T hC in
private theorem binary_linear_root_le_of_invariant
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (w : Weyl Q) (D : Subgroup (X ⧸ Q.D))
    (hD : Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set _))
    (a : X ⧸ Q.D) (ha : a ∈ rootAt Q split j w) (haD : a ∈ D) (han : a ≠ 1) :
    rootAt Q split j w ≤ D := by
  let A := rootAt Q split j w
  let ρ := rootAction Q split j w
  let := linear_rootAt_elementary Q split j n ν T hC w
  let : IsCyclic ρ.range := linear_rootAction_cyclic Q split j n ν T hC hn
    (UnitarySource.actorReflection Q split j) w
  intro b hb
  by_cases hb1 : b = 1
  · simpa only [hb1] using D.one_mem
  obtain ⟨c,hc,_⟩ := RootAction.regular_of_card ρ.range.subtype ρ.range.subtype_injective hn
    (linear_rootAction_card Q split j n ν T hC hn
      (UnitarySource.actorReflection Q split j) w)
    (linear_rootAt_card Q split j n ν T hC hn w)
    (⟨a,ha⟩ : A) ⟨b,hb⟩ (fun h => han (congrArg Subtype.val h))
    (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨h,hh⟩ := c.property
  have he : (h : X ⧸ Q.D)*a*(h : X ⧸ Q.D)⁻¹ = b := by
    have he := congrArg (fun f : MulAut A => (f ⟨a,ha⟩ : X ⧸ Q.D)) hh
    exact he.trans (congrArg Subtype.val hc)
  rw [←he]
  exact (mem_normalizer_iff.mp (hD h.property) a).mp haD

omit F [Field F] [Finite F] [CharP F 2] ν T hC in
include μ hB in
/-- The first assertion of source (6.4), including Sz(2). -/
theorem source_six_four_le_omega
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ ≤
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
  let V := simpleRemainder Q split i
  let D := (frattini V).map V.subtype
  let A := rootAt Q split i (Q.simple j*Q.simple i)
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  have hN : Endpoint Q i ≤ normalizer (D : Set _) :=
    source_frattini_parabolic_normalizes Q split i m μ hB
  have hΩ : omegaOneAmbient A ≤ D := source_omega_le_frattini Q split i m μ hB _
    (source_six_four_shifted_root_le_remainder Q split i j hm hij)
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hder : ⁅V,V⁆ ≤ D := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  intro z hz
  obtain ⟨_,a,ha,b,hb,hab⟩ :=
    source_six_four_product Q split i j m μ hB ν T hC hc hm hij hsize z hz
  have hb1 : b = 1 := by
    by_contra hbn
    let r := representative (Q.simple j*Q.simple i*Q.simple j)
    let e := (MulAut.conj (r : X ⧸ Q.D)).symm
    have he (K : Subgroup (X ⧸ Q.D)) : K.map e.toMonoidHom = rightConjugate K (r : X ⧸ Q.D) := by
      simp only [rightConjugate,comap_equiv_eq_map_symm']; rfl
    have ht := four_interval_reflection Q split hm i j hij r (representative_spec _)
    have hez : e z ∈ D := hder (four_interval_reflected_derived Q split hm i j hij r
      (representative_spec _) (by rw [←he]; exact ⟨z,hz,rfl⟩))
    have hea : e a ∈ omegaOneAmbient A := by
      have hh : (omegaOneAmbient A).map e.toMonoidHom = omegaOneAmbient A := by
        rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he,ht.2.1]
      rw [←hh]
      exact ⟨a,ha,rfl⟩
    have heb : e b ∈ C := by
      dsimp only [C]
      rw [←ht.1,←he]
      exact ⟨b,hb,rfl⟩
    have hebD : e b ∈ D := by
      have hh := D.mul_mem (D.inv_mem (hΩ hea)) hez
      rw [←hab,map_mul,inv_mul_cancel_left] at hh
      exact hh
    have hCD : C ≤ D := binary_linear_root_le_of_invariant Q split j n hn ν T hC _ D
      (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans hN))
      (e b) heb hebD (fun hh => hbn (e.injective (hh.trans (map_one e).symm)))
    have hzD : z ∈ D := by
      have hcomm : ⁅simpleRoot Q split i,C⁆ ≤ D :=
        (commutator_mono le_rfl hCD).trans (le_normalizer_iff_commutator_le_right.mp
          (((simpleRoot_le Q split i).trans
            (split.U_le.trans (Q.tits.B_le_standardParabolic _))).trans hN))
      exact hcomm hz
    have hbD : b ∈ D := by
      have hh := D.mul_mem (D.inv_mem (hΩ ha)) hzD
      rwa [←hab,inv_mul_cancel_left] at hh
    exact hbn (disjoint_def.mp
      (source_frattini_disjoint_first_linear Q split i j m μ hB ν T hC) hb hbD)
  simp only [hb1,mul_one] at hab
  rwa [←hab]

omit F [Field F] [Finite F] [CharP F 2] i j m μ hB ν T hC in
/-- Common-field specialization of both assertions of source (6.4).
The preceding odd-degree premise is retained. -/
theorem source_six_four_of_odd_degree
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hcore : Q.tits.B.normalCore = ⊥) :
    ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ ≤
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) ∧
    ⁅omegaOneAmbient (simpleRoot Q split 1),
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  have hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6 := by
    rw [show Nat.card (BinaryGaloisField n) = 2^n from GaloisField.card 2 n hn.pos.ne',he]
    exact Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide : 4 < 6)
  exact ⟨source_six_four_le_omega Q split 1 0 m μ hB n hn.pos ν T hC hc hm (by decide) hsize,
    source_six_four_omega_commute Q split 1 0 m μ hB ν T hC hc hm (by decide) hsize⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
