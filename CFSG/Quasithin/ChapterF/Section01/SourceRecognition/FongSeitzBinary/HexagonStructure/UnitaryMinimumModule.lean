module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree
public import Theory.Representation.SU3.NaturalTorus
public import Theory.Representation.SU3.MinimalBinaryDegree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitarySections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryCartanMarking
public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage

/-!
# The sharp unitary torus obstruction on the actual effective section

A nontrivial binary SU3 action of degree at most 6n is irreducible, and the
proved Chapter K catalogue identifies it with the natural module. Semilinear
coverage retains the full torus even when that identification twists the group
by an automorphism. Every nonzero vector consequently has more than 2^n images
under the literal full special-unitary torus.

The final theorem applies this to the original RootSection effective carrier,
using the actual special-unitary cover of R_j. It excludes the q-element
root-center subspaces in the source's q^7 derived configuration, once their
actual Cartan-stable image and nonzero vector have been placed in that carrier.
The full source Cartan marking is constructed internally, and faithfulness of
the original special cover follows from the sharp module identification.
The initial root-product configuration is constructed in UnitaryInitialEscape;
UnitaryPropagation supplies its subsequent lower-central argument.

Source: Fong--Seitz I (4D), printed pp.21--23, and (6D), printed pp.42--43.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {F V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- Every nonzero orbit under the literal full torus is larger than q,
including actions with an initially unspecified kernel. -/
theorem minimum_unitary_torus_orbit_card
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hne : ∃ g, ρ g ≠ 1) (hd : Module.finrank (ZMod 2) V ≤ 6*n)
    (W : Set V) (v : V) (hv : v≠0)
    (hW : ∀ k : Fˣ, ρ (hermitianTorusSU J hJ k) v ∈ W) :
    2^n < Nat.card W := by
  let : ρ.IsIrreducible := Representation.SU3.BinaryDegree.irreducible_of_finrank_le
    J hn hcard hconj ρ hne hd
  obtain ⟨a,E,hE⟩ := ChapterK.RankOne.UnitaryRecognition.MinimalDegree.isNatural_of_finrank_le
    J ρ hn hcard hconj hne hd
  obtain ⟨σ,u,hu⟩ := HermitianForm.EvenSemilinear.special_semilinear_coverage
    J hJ hn hcard hconj a
  let C : V ≃ₗ[ZMod 2] (Fin 3 → F) := E.trans
    ((Matrix.GeneralLinearGroup.toLin u.val⁻¹).toLinearEquiv.restrictScalars (ZMod 2))
  have hc (k : Fˣ) (v : V) : C (ρ (hermitianTorusSU J hJ k) v) =
      Matrix.mulVec (hermitianTorusSU J hJ (Units.map σ.toMonoidHom k)).val.val (C v) := by
    have hh : u.val⁻¹*(a (hermitianTorusSU J hJ k)).val =
        (hermitianTorusSU J hJ (Units.map σ.toMonoidHom k)).val*u.val⁻¹ := by
      rw [hu]
      change u.val⁻¹*(u.val*Matrix.GeneralLinearGroup.map σ.toRingHom
        (hermitianTorusGL J k)*u.val⁻¹) =
        hermitianTorusGL J (Units.map σ.toMonoidHom k)*u.val⁻¹
      rw [HermitianForm.BorelTorus.SemilinearActors.field_map_torus J σ k]
      group
    have hm := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) F =>
      Matrix.mulVec A.val (E v)) hh
    change Matrix.mulVec (u.val⁻¹).val (E (ρ (hermitianTorusSU J hJ k) v)) =
      Matrix.mulVec (hermitianTorusSU J hJ (Units.map σ.toMonoidHom k)).val.val
        (Matrix.mulVec (u.val⁻¹).val (E v))
    rw [hE]
    simpa only [Units.val_mul,Matrix.mulVec_mulVec] using hm
  have hm := Representation.SU3.NaturalTorus.card_lt_of_nonzero_orbit J hJ hn hcard hconj
    (C '' W) (C v) (fun he => hv (C.injective (he.trans C.map_zero.symm))) (by
      intro k
      let k' : Fˣ := Units.map σ.symm.toMonoidHom k
      have hk : Units.map σ.toMonoidHom k' = k := by ext; simp [k']
      rw [←hk,←hc]
      exact ⟨ρ (hermitianTorusSU J hJ k') v,hW k',rfl⟩)
  rwa [Nat.card_image_of_injective C.injective] at hm

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

/-- The sharp torus obstruction on the same effective quotient used in (5D).
The original nontrivial section action supplies nontriviality of its effective
binary action; the degree upper bound and a literal torus orbit then force size >q. -/
theorem unitary_effective_section_torus_orbit_card
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (d : RootSection Q split j) (hmove : d.action≠1)
    (hd : Nat.card d.EffectiveCarrier ≤ 2^(6*n))
    (W : Set (Additive d.EffectiveCarrier)) (v : Additive d.EffectiveCarrier) (hv : v≠0)
    (hW : ∀ k : Fˣ, d.effectiveRepresentation (σ (hermitianTorusSU J hJ k)) v ∈ W) :
    2^n < Nat.card W := by
  let ρ := d.effectiveRepresentation.comp σ
  have hne : ∃ g,ρ g≠1 := by
    by_contra! hh
    apply unitary_section_effectiveAction_ne_one Q split j J hn hcard hconj σ hσ d hmove
    apply MonoidHom.ext
    intro r
    obtain ⟨g,rfl⟩ := hσ r
    ext z
    have hz := congrArg (fun f : Module.End (ZMod 2) (Additive d.EffectiveCarrier) =>
      f (Additive.ofMul z)) (hh g)
    exact Additive.ofMul.injective hz
  have hc : Nat.card d.EffectiveCarrier =
      2^Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    change Nat.card (Additive d.EffectiveCarrier)=_
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive d.EffectiveCarrier))
  rw [hc] at hd
  have hdim := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hd
  exact minimum_unitary_torus_orbit_card J hJ hn hcard hconj ρ hne hdim W v hv hW


include hJ in
/-- A degree-6n effective section has no nonzero source-Cartan-invariant
subset of order at most q. The special cover is proved injective from the sharp
module classifier, then its actual Cartan is marked internally. -/
theorem unitary_effective_section_small_cartan_subset_false
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hroot : Nat.card (simpleRoot Q split j)=(2^n)^3)
    (d : RootSection Q split j) (hmove : d.action≠1)
    (hd : Nat.card d.EffectiveCarrier ≤ 2^(6*n))
    (W : Set (Additive d.EffectiveCarrier)) (hwcard : Nat.card W ≤ 2^n)
    (v : Additive d.EffectiveCarrier) (hv : v≠0) (hvm : v∈W)
    (hW : ∀ r : rankOne Q split j, (r : X ⧸ Q.D)∈Q.tits.B ⊓ Q.tits.N →
      ∀ w∈W, d.effectiveRepresentation r w∈W) : False := by
  let ρ:=d.effectiveRepresentation.comp σ
  have hne : ∃ g,ρ g≠1 := by
    by_contra! hh
    apply unitary_section_effectiveAction_ne_one Q split j J hn hcard hconj σ hσ d hmove
    apply MonoidHom.ext
    intro r
    obtain ⟨g,rfl⟩:=hσ r
    ext z
    have hz:=congrArg (fun f : Module.End (ZMod 2) (Additive d.EffectiveCarrier) =>
      f (Additive.ofMul z)) (hh g)
    exact Additive.ofMul.injective hz
  have hc : Nat.card d.EffectiveCarrier=
      2^Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    change Nat.card (Additive d.EffectiveCarrier)=_
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive d.EffectiveCarrier))
  have hdim : Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) ≤ 6*n := by
    rw [hc] at hd
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hd
  let : Representation.IsIrreducible ρ := Representation.SU3.BinaryDegree.irreducible_of_finrank_le
    J hn hcard hconj ρ hne hdim
  have hnat:=ChapterK.RankOne.UnitaryRecognition.MinimalDegree.isNatural_of_finrank_le
    J ρ hn hcard hconj hne hdim
  have hσi : Function.Injective σ := by
    intro a b he
    exact hnat.injective J (congrArg d.effectiveRepresentation he)
  let μ := (MulEquiv.ofBijective σ ⟨hσi,hσ⟩).symm
  obtain ⟨e,he⟩:=exists_special_unitary_cartan_marking J hJ Q split hn hcard hconj j hK μ hroot
  have horbit (k : Fˣ) : d.effectiveRepresentation (e.symm (hermitianTorusSU J hJ k)) v∈W := by
    apply hW _ _ v hvm
    have hm : hermitianTorusSU J hJ k ∈
        ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)).map e.toMonoidHom := by
      rw [he]
      exact ⟨k,rfl⟩
    obtain ⟨r,hr,her⟩:=hm
    have hr' : e.symm (hermitianTorusSU J hJ k)=r := by rw [←her]; exact e.symm_apply_apply r
    rwa [hr']
  have hh:=unitary_effective_section_torus_orbit_card J hJ Q split j hn hcard hconj
    e.symm.toMonoidHom e.symm.surjective d hmove hd W v hv horbit
  omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
