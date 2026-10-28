module

public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.SubgroupConjugation

/-!
# Transport and generation of action supports

Action commutators commute with conjugation of the actor and with joins of
acting subgroups. The proofs use the generating displacements v⁻¹(a • v).
These general arguments are adapted from
`Stellmacher/SectionOne/RankOneThreeGroupAssembly/Basic.lean` and
`OmegaFixedIndices.lean`, where they support Stellmacher (1.6).
-/

namespace ActionSupport

/-- Conjugating an acting subgroup transports its action commutator by the
same ambient automorphism of the module. -/
public theorem commutatorAction_conjBy
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (F : Subgroup G) (g : G) :
    (commutatorAction F V).map
        (MulDistribMulAction.toMulAut G V g).toMonoidHom =
      commutatorAction (F.conjBy g) V := by
  rw [commutatorAction_eq_closure, MonoidHom.map_closure,
    commutatorAction_eq_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y, ⟨f, v, rfl⟩, rfl⟩
    let fg : F.conjBy g :=
      ⟨g * (f : G) * g⁻¹, ⟨(f : G), f.property, rfl⟩⟩
    refine ⟨fg, g • v, ?_⟩
    change g • (v⁻¹ * (f : G) • v) =
      (g • v)⁻¹ * (g * (f : G) * g⁻¹) • (g • v)
    simp only [smul_mul', smul_inv', smul_smul]
    congr 1
    group
  · rintro ⟨fg, v, rfl⟩
    rcases fg.property with ⟨f, hf, hfg⟩
    let fF : F := ⟨f, hf⟩
    refine ⟨(g⁻¹ • v)⁻¹ * (fF : G) • (g⁻¹ • v), ⟨fF, g⁻¹ • v, rfl⟩, ?_⟩
    change g • ((g⁻¹ • v)⁻¹ * f • (g⁻¹ • v)) =
      v⁻¹ * (fg : G) • v
    rw [← hfg]
    simp [smul_mul', smul_inv', smul_smul, MulAut.conj_apply, mul_assoc]

public theorem commutatorAction_eq_iSup_of_eq_iSup
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    {A : Subgroup G} {I : Sort*} (K : I → Subgroup G)
    (hA : A = ⨆ i, K i) :
    commutatorAction A V = ⨆ i, commutatorAction (K i) V := by
  apply le_antisymm
  · let U : Subgroup V := ⨆ i, commutatorAction (K i) V
    let P : Subgroup G :=
      { carrier := {a : G | ∀ w : V, w⁻¹ * (a • w) ∈ U}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb w
          have hbmem := hb w
          have hamem := ha (b • w)
          have hmul : w⁻¹ * ((a * b) • w) =
              (w⁻¹ * (b • w)) * ((b • w)⁻¹ * (a • (b • w))) := by
            simp [smul_smul, mul_assoc]
          rw [hmul]
          exact U.mul_mem hbmem hamem
        inv_mem' := by
          intro a ha w
          have hmem := ha (a⁻¹ • w)
          have hinv : w⁻¹ * (a⁻¹ • w) =
              ((a⁻¹ • w)⁻¹ * (a • (a⁻¹ • w)))⁻¹ := by
            simp [smul_smul]
          rw [hinv]
          exact U.inv_mem hmem }
    have hKleP (i : I) : K i ≤ P := by
      intro a ha w
      apply (show commutatorAction (K i) V ≤ U from
        le_iSup (fun j => commutatorAction (K j) V) i)
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨a, ha⟩, w, rfl⟩
    have hAleP : A ≤ P := by
      rw [hA]
      exact iSup_le hKleP
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := U)).2 ?_
    rintro x ⟨a, w, rfl⟩
    exact hAleP a.property w
  · refine iSup_le ?_
    intro i
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro x ⟨a, w, rfl⟩
    refine ⟨⟨a, ?_⟩, w, rfl⟩
    rw [hA]
    exact le_iSup (fun j => K j) i a.property

end ActionSupport
