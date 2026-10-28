module
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Frattini.PGroup
public import Theory.GroupAction.CoprimeHall
public import Theory.Representation.Maschke
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.IntegralDomain

/-!
# Fixed-point generation for a coprime abelian action on a p-group

A finite abelian actor group of order coprime to q generates a finite
q-group through the fixed subgroups of those actor subgroups whose quotient
is cyclic. The original supplied action is retained. The actor group need
not be noncyclic or a p-group, and no faithfulness assumption is imposed.

For an elementary abelian q-group, Maschke's theorem decomposes its group
algebra module into simple modules. Each simple module is a quotient by a
maximal ideal, so its actor image lies in the unit group of a field and is
cyclic. The kernel fixes that simple summand, and the summands generate the
module. For a general q-group, apply this argument to its elementary
Frattini quotient. Coprime fixed-point lifting identifies the quotient
fixed groups with the images of the original fixed groups. The Frattini
non-generating property then lifts generation to the whole group.

This is the source-neutral proof underlying the cyclic-quotient step of
Feit–Thompson background Proposition (1.16)(b), extracted from
FeitThompson.GroupAction.NoncyclicAbelianPGroup. Its original public
consumers retain their interfaces, while the reusable statement also
supplies Stellmacher (8.6)(21)'s rank-three binary-action argument.
-/

open scoped Pointwise

private theorem exists_cyclic_quotient_fix_of_simple
    {k A S : Type*} [Field k] [Finite k] [CommGroup A] [Finite A]
    [AddCommGroup S] [Module (MonoidAlgebra k A) S]
    [IsSimpleModule (MonoidAlgebra k A) S] :
    ∃ Y : Subgroup A, IsCyclic (A ⧸ Y) ∧
      ∀ y : Y, ∀ x : S, (MonoidAlgebra.of k A (y : A)) • x = x := by
  classical
  obtain ⟨I, _, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra k A) (M := S)).mp inferInstance
  let _ : Field (MonoidAlgebra k A ⧸ I) := Ideal.Quotient.field I
  let φ : A →* (MonoidAlgebra k A ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I)).comp (MonoidHom.toHomUnits (MonoidAlgebra.of k A))
  let _ : Finite ↥φ.range :=
    Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  refine ⟨φ.ker, ?_, ?_⟩
  · have hrange_cyc : IsCyclic ↥φ.range := isCyclic_subgroup_units φ.range
    exact (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange φ)).2 hrange_cyc
  · intro y x
    apply e.injective
    have hy : Ideal.Quotient.mk I ((MonoidAlgebra.of k A) (y : A)) = 1 := by
      exact congrArg (fun u : (MonoidAlgebra k A ⧸ I)ˣ => (u : MonoidAlgebra k A ⧸ I)) y.2
    have hy' : Ideal.Quotient.mk I (MonoidAlgebra.single (y : A) 1 : MonoidAlgebra k A) = 1 := by
      simpa [MonoidAlgebra.of] using hy
    calc
      e (((MonoidAlgebra.of k A) (y : A)) • x) = ((MonoidAlgebra.of k A) (y : A)) • e x := by
        exact e.map_smul ((MonoidAlgebra.of k A) (y : A)) x
      _ = (Ideal.Quotient.mk I (MonoidAlgebra.single (y : A) 1 : MonoidAlgebra k A)) * e x := by
        rfl
      _ = e x := by
        rw [hy', one_mul]

private theorem isSemisimpleModule_groupAlgebra_zmod
    {A : Type*} [CommGroup A] [Finite A] {q : ℕ} [Fact q.Prime]
    (hq : Nat.Coprime (Nat.card A) q) {V : Type*} [AddCommGroup V]
    [Module (MonoidAlgebra (ZMod q) A) V] :
    IsSemisimpleModule (MonoidAlgebra (ZMod q) A) V := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  have hq' : Nat.Coprime (Fintype.card A) q := by
    simpa [Nat.card_eq_fintype_card] using hq
  have _ : NeZero (Fintype.card A : ZMod q) := by
    constructor
    intro hzero
    have hdiv : q ∣ Fintype.card A := (ZMod.natCast_eq_zero_iff (Fintype.card A) q).1 hzero
    exact (((Fact.out : q.Prime).coprime_iff_not_dvd).1 hq'.symm) hdiv
  infer_instance

private theorem proposition_1_16_b_elementaryAbelian
    {G A : Type*} [CommGroup G] [Finite G] {q : ℕ} [Fact q.Prime] [IsElementaryAbelian q G]
    [CommGroup A] [Finite A] [MulDistribMulAction A G]
    (hqA : Nat.Coprime (Nat.card A) q) :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤ := by
  classical
  let ρ : Representation (ZMod q) A (Additive G) := {
    toFun := fun a =>
      let eAdd : Additive G ≃+ Additive G :=
        MulEquiv.toAdditive (MulDistribMulAction.toMulAut A G a)
      let eLin : Additive G ≃ₗ[ZMod q] Additive G :=
        eAdd.toLinearEquiv (fun c x => by
          simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
      eLin.toLinearMap
    map_one' := by
      ext x
      apply Additive.toMul.injective
      simp [MulDistribMulAction.toMulAut]
    map_mul' := by
      intro a b
      ext x
      apply Additive.toMul.injective
      simp [MulDistribMulAction.toMulAut, smul_smul] }
  let _ : AddCommMonoid ρ.asModule := Representation.instAddCommMonoidAsModule ρ
  let _ : Module (ZMod q) ρ.asModule := Representation.instModuleAsModule ρ
  let _ : Module (MonoidAlgebra (ZMod q) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  let η : Subgroup G ≃o Submodule (ZMod q) (Additive G) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := q))
  let Y1 : Type _ := {Y : Subgroup A // IsCyclic (A ⧸ Y)}
  let p : Y1 → Submodule (ZMod q) (Additive G) := fun Y =>
    η (fixedPointSubgroup (↥Y.1) G)
  have hBinv : ∀ Y : Subgroup A, η (fixedPointSubgroup (↥Y) G) ∈ ρ.invtSubmodule := by
    intro Y
    rw [Representation.mem_invtSubmodule]
    intro b
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change b • Additive.toMul x ∈ fixedPointSubgroup (↥Y) G
    rw [FixedPoints.mem_subgroup]
    intro z
    have hxfix : ((z : A) • Additive.toMul x) = Additive.toMul x := by
      change Additive.toMul x ∈ fixedPointSubgroup (↥Y) G at hx
      rw [FixedPoints.mem_subgroup] at hx
      simpa only [Subgroup.smul_def] using hx z
    have hcomm : Commute ((z : Y) : A) b := by
      exact Commute.all _ _
    change ((z : A) • (b • Additive.toMul x)) = b • Additive.toMul x
    calc
      ((z : A) • (b • Additive.toMul x)) = (((z : Y) : A) * b) • Additive.toMul x := by
        exact smul_smul ((z : Y) : A) b (Additive.toMul x)
      _ = (b * ((z : Y) : A)) • Additive.toMul x := by simp [hcomm.eq]
      _ = b • (((z : Y) : A) • Additive.toMul x) := by
        exact (smul_smul b ((z : Y) : A) (Additive.toMul x)).symm
      _ = b • Additive.toMul x := by simp [hxfix]
  let H : Subgroup G := ⨆ Y : Y1, fixedPointSubgroup (↥Y.1) G
  let L : Submodule (ZMod q) (Additive G) := ⨆ Y : Y1, p Y
  have hLinv : L ∈ ρ.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro b
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    refine Submodule.iSup_induction p (motive := fun y => (ρ b) y ∈ L) hx ?_ ?_ ?_
    · intro Y y hy
      have hpYInv := hBinv Y.1
      rw [Representation.mem_invtSubmodule] at hpYInv
      exact Submodule.mem_iSup_of_mem Y <|
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ b)).1 (hpYInv b) y hy
    · simp
    · intro y z hy hz
      simpa [map_add] using (L.add_mem hy hz)
  let K : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule := ρ.mapSubmodule ⟨L, hLinv⟩
  let hs :=
    @isSemisimpleModule_groupAlgebra_zmod A inferInstance inferInstance q inferInstance hqA
      ρ.asModule (Representation.instAddCommGroupAsModule ρ)
      (Representation.instModuleMonoidAlgebraAsModule ρ)
  have htople : (⊤ : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule) ≤ K := by
    calc
      (⊤ : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule)
          = sSup {S : Submodule (MonoidAlgebra (ZMod q) A) ρ.asModule |
              IsSimpleModule (MonoidAlgebra (ZMod q) A) S} := by
                symm
                exact @IsSemisimpleModule.sSup_simples_eq_top
                  (MonoidAlgebra (ZMod q) A) inferInstance ρ.asModule
                  (Representation.instAddCommGroupAsModule ρ)
                  (Representation.instModuleMonoidAlgebraAsModule ρ) hs
      _ ≤ K := by
            refine sSup_le ?_
            intro S hS
            let _ : IsSimpleModule (MonoidAlgebra (ZMod q) A) S := hS
            obtain ⟨Y, hYcyc, hfix⟩ :=
              exists_cyclic_quotient_fix_of_simple (k := ZMod q) (A := A) (S := S)
            let Y1' : Y1 := ⟨Y, hYcyc⟩
            have hSle : S ≤ ρ.mapSubmodule ⟨p Y1', hBinv Y⟩ := by
              have hle' : (ρ.mapSubmodule.symm S : Submodule (ZMod q) (Additive G)) ≤ p Y1' := by
                intro x hx
                change Additive.toMul x ∈ fixedPointSubgroup (↥Y) G
                rw [FixedPoints.mem_subgroup]
                intro y
                have hyfix : ((y : Y) : A) • Additive.toMul x = Additive.toMul x := by
                  have hfix' :
                      (MonoidAlgebra.of (ZMod q) A ((y : Y) : A)) • ρ.asModuleEquiv.symm x =
                        ρ.asModuleEquiv.symm x := by
                    exact congrArg Subtype.val (hfix y ⟨ρ.asModuleEquiv.symm x, hx⟩)
                  have hfixρ_asModule :
                      ρ.asModuleEquiv.symm (ρ ((y : Y) : A) x) = ρ.asModuleEquiv.symm x := by
                    rw [Representation.asModuleEquiv_symm_map_rho]
                    exact hfix'
                  have hfixρ : ρ ((y : Y) : A) x = x :=
                    ρ.asModuleEquiv.symm.injective hfixρ_asModule
                  simpa [ρ, MulDistribMulAction.toMulAut] using congrArg Additive.toMul hfixρ
                change ((y : A) • Additive.toMul x) = Additive.toMul x
                exact hyfix
              have hle'' : ρ.mapSubmodule.symm S ≤ ⟨p Y1', hBinv Y⟩ := hle'
              simpa using ρ.mapSubmodule.monotone hle''
            have hsub : (⟨p Y1', hBinv Y⟩ : ρ.invtSubmodule) ≤ ⟨L, hLinv⟩ := by
              exact show p Y1' ≤ L by exact le_iSup (fun Y => p Y) Y1'
            exact hSle.trans (ρ.mapSubmodule.monotone hsub)
  have hKtop : K = ⊤ := top_le_iff.mp htople
  have hLtoppack : (⟨L, hLinv⟩ : ρ.invtSubmodule) = ⊤ := by
    apply ρ.mapSubmodule.injective
    simpa [K] using hKtop
  have hLtop : L = ⊤ := by
    simpa using congrArg Subtype.val hLtoppack
  have hηH : η H = ⊤ := by
    calc
      η H = ⨆ Y : Y1, η (fixedPointSubgroup (↥Y.1) G) := by simp [H]
      _ = ⨆ Y : Y1, p Y := by rfl
      _ = ⊤ := hLtop
  have hHtop : H = ⊤ := η.injective hηH
  simpa [H, Y1, iSup_subtype] using hHtop

public theorem iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    {G A : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q G)]
    [CommGroup A] [Finite A] [MulDistribMulAction A G]
    (hAq : Nat.Coprime (Nat.card A) q) :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), FixedPoints.subgroup Y G) = ⊤ := by
  classical
  let Y1 : Type _ := {Y : Subgroup A // IsCyclic (A ⧸ Y)}
  let K : Subgroup G := ⨆ Y : Y1, fixedPointSubgroup (↥Y.1) G
  have hcopG : Nat.Coprime (Nat.card A) (Nat.card G) := by
    obtain ⟨n, hn⟩ := (Fact.out : IsPGroup q G).exists_card_eq
    rw [hn]
    exact hAq.pow_right n
  have hsolv : Group.IsSolvable G := by
    exact @IsNilpotent.to_isSolvable G inferInstance ((Fact.out : IsPGroup q G).isNilpotent)
  let hfrattini_inv : IsInvariant A G (frattini G) :=
    isInvariant_of_characteristic (A := A) (G := G) (frattini G)
  let _ : MulAction.QuotientAction A (frattini G) :=
    quotientAction_of_isInvariant (A := A) (frattini G) hfrattini_inv
  let _ : MulDistribMulAction A (G ⧸ frattini G) :=
    quotientMulDistribMulAction (A := A) (G := G) (frattini G) hfrattini_inv
  let Kbar : Subgroup (G ⧸ frattini G) :=
    ⨆ Y : Y1, fixedPointSubgroup (↥Y.1) (G ⧸ frattini G)
  have hKbar_eq : K.map (QuotientGroup.mk' (frattini G)) = Kbar := by
    calc
      K.map (QuotientGroup.mk' (frattini G))
          = ⨆ Y : Y1,
              (fixedPointSubgroup (↥Y.1) G).map
                (QuotientGroup.mk' (frattini G)) := by
            simp [K, Subgroup.map_iSup]
      _ = Kbar := by
            apply iSup_congr
            intro Y
            have hsubcop :
                Nat.Coprime (Nat.card ↥Y.1) (Nat.card G) := by
              exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card Y.1) hcopG
            have hsubinv : IsInvariant ↥Y.1 G (frattini G) := by
              constructor
              intro z g
              change (g ∈ frattini G) ↔ (((z : Y.1) : A) • g ∈ frattini G)
              exact hfrattini_inv.invariant ((z : Y.1) : A) g
            let _ : MulAction.QuotientAction ↥Y.1 (frattini G) :=
              quotientAction_of_isInvariant (A := ↥Y.1) (frattini G) hsubinv
            let _ : MulDistribMulAction ↥Y.1 (G ⧸ frattini G) :=
              quotientMulDistribMulAction (A := ↥Y.1) (G := G) (frattini G) hsubinv
            simpa [Kbar] using
              (fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
                (G := G) (A := ↥Y.1) hsolv hsubcop
                (frattini G) hsubinv).symm
  have _ : IsElementaryAbelian q (G ⧸ frattini G) :=
    isElementaryAbelian_quotient_frattini (R := G) (p := q)
  have hKbar_top : Kbar = ⊤ := by
    let _ : CommGroup (G ⧸ frattini G) := IsMulCommutative.instCommGroup
    simpa [Kbar, Y1, iSup_subtype] using
      proposition_1_16_b_elementaryAbelian (G := G ⧸ frattini G) (A := A) (q := q) hAq
  have hKsup : K ⊔ frattini G = ⊤ := by
    apply top_unique
    intro g _
    have hgbar : ((g : G) : G ⧸ frattini G) ∈ K.map (QuotientGroup.mk' (frattini G)) := by
      simp [hKbar_eq, hKbar_top]
    rcases hgbar with ⟨k, hkK, hkg⟩
    have hkgΦ : k⁻¹ * g ∈ frattini G := by
      apply (QuotientGroup.eq_one_iff (N := frattini G) (x := k⁻¹ * g)).1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have hkg' : (k : G ⧸ frattini G) = (g : G ⧸ frattini G) := hkg
      rw [hkg']
      simp
    exact (Subgroup.mem_sup_of_normal_right (s := K) (t := frattini G) (x := g)).2
      ⟨k, hkK, k⁻¹ * g, hkgΦ, by simp⟩
  have hKtop : K = ⊤ := frattini_nongenerating_of_isPGroup (R := G) (p := q) K hKsup
  simpa [K, Y1, iSup_subtype] using hKtop


