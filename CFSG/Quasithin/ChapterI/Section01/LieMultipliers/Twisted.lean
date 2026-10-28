module

public import Theory.GroupTheory.PerfectCentralCoverTrivialTransport
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Triality.CentralCovers.PrimaryAssembly
public import Theory.SpecificGroups.ReeF4.DerivedTits.Reduction
public import Theory.SpecificGroups.Tits.CentralCoverLifting

/-!
# Assembly for the twisted exceptional multiplier cases

The genuine binary triality carriers, large Ree fixed-point carriers, and
Parrott's Tits group are the three remaining twisted cases of the vanishing
assertion in Aschbacher–Smith I.1.3–I.1.4. Triality includes exponent one;
the Ree family has parameter `m ≥ 1`; its full nonsimple `Model 0` is not
the simple Tits endpoint.

These are conditional assembly theorems. The triality and Ree canonical
kernel calculations and the compatible Parrott generator lifts are explicit
independent inputs. From them we obtain the canonical kernel for any actual
model isomorphism, the identity-cover universal property, and the kernel of
any chosen universal covering. The component application retains the literal
map to the central quotient. None of these conditional results alone proves
the source multiplier assertion.

The Ree calculation may use perfectness inherited from the source group;
the assembly proves that hypothesis via its actual model isomorphism. Tits
perfectness is supplied by the certified presentation, not by a new premise.

Sources: Aschbacher–Smith A.2.2–A.2.4, printed p.33 (PDF p.44), and
I.1.1–I.1.4, printed pp.407–408 (PDF pp.418–419); GLS3 §6.1,
especially Tables 6.1.2–6.1.3 and Theorem 6.1.4. Algebraic simply connectedness
does not establish any of the finite universal-kernel inputs below.
-/

public section

namespace CFSG.Quasithin.ChapterI.LieMultipliers.Twisted

open Theory.GroupTheory PerfectCentralCovering

universe u w

/-- Compatible lifts of the named presentation give the exact Tits kernel
required by the small-derived-cover consumer. Perfectness is discharged. -/
theorem tits_universalProjection_ker_eq_bot_of_lifts
    (hlifts : ∃ g : Tits.ParrottGenerator → UniversalGroup Tits.ParrottGroup,
      Tits.SatisfiesParrottRelations g ∧
        ∀ i, universalProjection Tits.ParrottGroup (g i) = Tits.parrottGenerator i) :
    (universalProjection Tits.ParrottGroup).ker = ⊥ := by
  let : Group.IsPerfect Tits.ParrottGroup := ReeF4.DerivedTits.parrott_perfect
  exact Tits.CentralCoverLifting.universalProjection_ker_eq_bot_of_lifts hlifts

variable
  (htriality : ∀ (f : ℕ) (hf : 0 < f),
    (universalProjection (Triality.Standard.BinaryCarrier f hf)).ker = ⊥)
  (hree : ∀ (m : ℕ), 1 ≤ m → Group.IsPerfect (ReeF4.Model m) →
    (universalProjection (ReeF4.Model m)).ker = ⊥)
  (htits : ∃ g : Tits.ParrottGenerator → UniversalGroup Tits.ParrottGroup,
    Tits.SatisfiesParrottRelations g ∧
      ∀ i, universalProjection Tits.ParrottGroup (g i) = Tits.parrottGenerator i)

include htriality hree htits

/-- Assemble the three independent calculations at the genuine source models.
All isomorphisms are actual multiplicative equivalences; no auxiliary
three-coordinate triality group is used. -/
theorem universalProjection_ker_eq_bot_of_model_calculations
    {G : Type u} [Group G] [Group.IsPerfect G]
    (hmodel : Triality.IsQTKETrialityModel G ∨ ReeF4.IsReeF4Model G ∨
      Nonempty (G ≃* Tits.ParrottGroup)) :
    (universalProjection G).ker = ⊥ := by
  rcases hmodel with htrialModel | hrest
  · obtain ⟨f, hf, ⟨e⟩⟩ := htrialModel
    exact universalProjection_ker_eq_bot_of_mulEquiv e (htriality f hf)
  · rcases hrest with hreeModel | htitsModel
    · obtain ⟨m, hm, ⟨e⟩⟩ := hreeModel
      have hp : Group.IsPerfect (ReeF4.Model m) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      exact universalProjection_ker_eq_bot_of_mulEquiv e (hree m hm hp)
    · obtain ⟨e⟩ := htitsModel
      exact universalProjection_ker_eq_bot_of_mulEquiv e
        (tits_universalProjection_ker_eq_bot_of_lifts htits)

/-- The identity covering is universal once the three family calculations
are supplied. The base's finiteness and quasisimplicity are the original
covering hypotheses, with no additional model assumptions. -/
theorem identity_isUniversal_of_model_calculations
    {G : Type u} [Group G] [Finite G] [IsQuasisimple G]
    (hmodel : Triality.IsQTKETrialityModel G ∨ ReeF4.IsReeF4Model G ∨
      Nonempty (G ≃* Tits.ParrottGroup)) :
    Covering.IsUniversal.{u, u, w} (Covering.id : Covering G G) := by
  apply Covering.isUniversal_of_kernel_card_le
  rw [Subgroup.card_eq_one.mpr
    (universalProjection_ker_eq_bot_of_model_calculations htriality hree htits hmodel)]
  exact Nat.card_pos

/-- Comparison with the identity cover computes the kernel of any chosen
universal covering, including its group structure. -/
noncomputable def universalKernelEquivPUnitOfModelCalculations
    {G E : Type u} [Group G] [Finite G] [IsQuasisimple G]
    [Group E] [Finite E] [IsQuasisimple E]
    (hmodel : Triality.IsQTKETrialityModel G ∨ ReeF4.IsReeF4Model G ∨
      Nonempty (G ≃* Tits.ParrottGroup))
    (c : Covering E G) (hc : Covering.IsUniversal.{u, u, u} c) :
    c.toMonoidHom.ker ≃* PUnit := by
  let e := hc.kerMulEquiv
    (identity_isUniversal_of_model_calculations htriality hree htits hmodel)
    (MulEquiv.refl G)
  have hk : (Covering.id : Covering G G).toMonoidHom.ker = ⊥ := by
    simp only [Covering.id_toMonoidHom, MonoidHom.ker_id]
  let : Subsingleton (Covering.id : Covering G G).toMonoidHom.ker := by
    rw [hk]
    infer_instance
  let : Unique (Covering.id : Covering G G).toMonoidHom.ker := uniqueOfSubsingleton 1
  exact e.trans MulEquiv.ofUnique

/-- Application to a source component: its literal central quotient forces
its entire center to vanish after the family calculations are supplied. -/
theorem center_eq_bot_of_model_calculations
    {L : Type u} [Group L] [Group.IsPerfect L]
    (hmodel : Triality.IsQTKETrialityModel (L ⧸ Subgroup.center L) ∨
      ReeF4.IsReeF4Model (L ⧸ Subgroup.center L) ∨
      Nonempty (L ⧸ Subgroup.center L ≃* Tits.ParrottGroup)) :
    Subgroup.center L = ⊥ :=
  center_eq_bot_of_centralQuotientEquiv
    (universalProjection_ker_eq_bot_of_model_calculations htriality hree htits hmodel)
    (MulEquiv.refl _)

/-- The component's whole-group model follows through its original central
projection, with the quotient triangle explicitly preserved. -/
theorem exists_whole_quotient_equiv_of_model_calculations
    {L : Type u} [Group L] [Group.IsPerfect L]
    (hmodel : Triality.IsQTKETrialityModel (L ⧸ Subgroup.center L) ∨
      ReeF4.IsReeF4Model (L ⧸ Subgroup.center L) ∨
      Nonempty (L ⧸ Subgroup.center L ≃* Tits.ParrottGroup)) :
    ∃ e : L ≃* L ⧸ Subgroup.center L,
      ∀ x, e x = QuotientGroup.mk' (Subgroup.center L) x := by
  have hk := universalProjection_ker_eq_bot_of_model_calculations
    htriality hree htits hmodel
  exact ⟨centralQuotientEquivOfUniversalKernelEqBot hk (MulEquiv.refl _),
    fun x => centralQuotientEquivOfUniversalKernelEqBot_apply hk (MulEquiv.refl _) x⟩

omit htriality in
/-- Reuse the existing odd-center owner and the independent two-primary
calculation in the three-family source assembly. The canonical triality
cover's finiteness, quasisimplicity and quotient model are all discharged. -/
theorem universalProjection_ker_eq_bot_of_primary_calculations
    (hodd : ∀ (n : ℕ), 0 < n →
      ∀ (R : Type) [Group R] [Finite R] [IsQuasisimple R],
        Triality.Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R) →
        IsPGroup 2 (Subgroup.center R))
    (htwo : ∀ (n : ℕ) (hn : 0 < n),
      ¬ 2 ∣ Nat.card (universalProjection (Triality.Standard.BinaryCarrier n hn)).ker)
    {G : Type u} [Group G] [Group.IsPerfect G]
    (hmodel : Triality.IsQTKETrialityModel G ∨ ReeF4.IsReeF4Model G ∨
      Nonempty (G ≃* Tits.ParrottGroup)) :
    (universalProjection G).ker = ⊥ :=
  universalProjection_ker_eq_bot_of_model_calculations
    (fun n hn => Triality.Standard.CentralCovers.universalProjection_ker_eq_bot_of_primary_calculations
      n hn (hodd n hn) (htwo n hn)) hree htits hmodel

end CFSG.Quasithin.ChapterI.LieMultipliers.Twisted
