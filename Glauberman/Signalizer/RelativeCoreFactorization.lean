module

public import Theory.GroupTheory.PPrimeCoreSupplement
public import Theory.GroupTheory.Signalizer.Conjugation
public import Theory.GroupAction.FixedCoprimeSupplement
public import Glauberman.Signalizer.NormalizerSupplement

/-!
# Relative core factorizations inside a signalizer normalizer

For an odd solvable signalizer family under the supplied elementary binary
actor, suppose M is supplemented by its q′-core and L intersect M,
and U is supplemented by its q′-core and U intersect M. Let W be a
q-signalizer subgroup of M. If U lies in the normalizer of W and contains
M intersect that normalizer, then an element c of the actual common
signalizer subgroup intersect M gives U = core(U) joined with U intersect
L^c. No nontriviality of W, rank bound, or global local-completeness
hypothesis is required; the two explicit normalizer bounds are the local
properties needed by the proof.

Invariant Sylow conjugacy inside M places W in a fixed conjugate of the
supplement L intersect M. Fixedness and the signalizer bounds put c in
every family value. The proved coprime normal-supplement normalizer
formula then factors U intersect M. To absorb its extra q′-factor,
the existing core-supplement theorem identifies the core of U intersect M
with the corresponding intersection of the U-core. Thus U intersect
core(M) lies in core(U), and the desired factorization follows.

This is Kurzweil–Stellmacher, *The Theory of Finite Groups*, 11.2.6,
printed p. 321. All subgroup cores are the actual native cores mapped by
their subtype homomorphisms; all restrictions retain the supplied action.
The final absorption uses the stronger proved core-supplement identity
instead of repeating the source's normality argument for three factors.
-/



namespace Glauberman

open Theory.GroupTheory

/-- The relative core factorization of KS 11.2.6, with its exact local
normalizer bounds and a conjugator in the family's common subgroup. -/
public theorem relative_signalizer_core_factorization
    {A G : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group G] [Finite G] [MulDistribMulAction A G]
    (θ : TwoSignalizerFamily A G) {q : ℕ} [Fact q.Prime]
    (L M U W : Subgroup G)
    (hL : θ.IsSignalizerSubgroup L) (hM : θ.IsSignalizerSubgroup M)
    (_hU : θ.IsSignalizerSubgroup U) (hW : θ.IsSignalizerSubgroup W)
    (hWq : IsPGroup q W) (hWM : W ≤ M)
    (hUN : U ≤ Subgroup.normalizer (W : Set G))
    (hMN : M ⊓ Subgroup.normalizer (W : Set G) ≤ U)
    (hMfactor : M = (pPrimeCore q M).map M.subtype ⊔ (L ⊓ M))
    (hUfactor : U = (pPrimeCore q U).map U.subtype ⊔ (U ⊓ M)) :
    ∃ c : G, c ∈ θ.common ⊓ M ∧
      U = (pPrimeCore q U).map U.subtype ⊔
        (U ⊓ L.map (MulAut.conj c : G →* G)) := by
  let _ : IsInvariant A G L := hL.2.2.1
  let _ : IsInvariant A G M := hM.2.2.1
  let _ : IsInvariant A G W := hW.2.2.1
  let B : Subgroup M := L.subgroupOf M
  let V : Subgroup M := W.subgroupOf M
  have hsup : pPrimeCore q M ⊔ B = ⊤ := by
    apply Subgroup.map_injective (f := M.subtype) M.subtype_injective
    rw [Subgroup.map_sup]
    change (pPrimeCore q M).map M.subtype ⊔ (L.subgroupOf M).map M.subtype = _
    rw [Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hMfactor.symm
  have hVq : IsPGroup q V := hWq.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  obtain ⟨c, hcfix, hVD⟩ := exists_fixedPoint_conj_le_of_coprime_normal_supplement
    (IsElementaryAbelian.isPGroup 2 A) hM.1 hM.2.1
    (pPrimeCore q M) B V pPrimeCore_coprime_card hsup
    (isInvariant_subgroupOf L M) hVq (isInvariant_subgroupOf W M)
  have hccommon : (c : G) ∈ θ.common := by
    apply Subgroup.mem_iInf.mpr
    intro a
    apply hM.2.2.2 a
    exact ⟨c.property, fun z => congrArg Subtype.val (hcfix z.val)⟩
  let D : Subgroup M := B.map (MulAut.conj c : M →* M)
  let Lc : Subgroup G := L.map (MulAut.conj (c : G) : G →* G)
  have hCmap : (pPrimeCore q M).map (MulAut.conj c : M →* M) = pPrimeCore q M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (by
      rw [Subgroup.normalizer_eq_top]
      trivial)
  have hDsup : pPrimeCore q M ⊔ D = ⊤ := by
    have hh := congrArg (fun X : Subgroup M => X.map (MulAut.conj c : M →* M)) hsup
    rw [Subgroup.map_sup, hCmap,
      Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective] at hh
    exact hh
  have hfactor := normalizer_eq_inf_sup_inf_of_coprime_normal_supplement
    (pPrimeCore q M) D V pPrimeCore_coprime_card hDsup hVq hVD
  have hNmap : (Subgroup.normalizer (V : Set M)).map M.subtype =
      M ⊓ Subgroup.normalizer (W : Set G) := by
    change (Subgroup.normalizer (W.subgroupOf M : Set M)).map M.subtype = _
    rw [← Subgroup.subgroupOf_normalizer_eq hWM, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hUM : U ⊓ M = (Subgroup.normalizer (V : Set M)).map M.subtype := by
    rw [hNmap]
    exact le_antisymm (le_inf inf_le_right (inf_le_left.trans hUN))
      (le_inf hMN inf_le_left)
  have hNG (m : M) (hm : m ∈ Subgroup.normalizer (V : Set M)) :
      (m : G) ∈ Subgroup.normalizer (W : Set G) := by
    have hh : (m : G) ∈ (Subgroup.normalizer (V : Set M)).map M.subtype := ⟨m, hm, rfl⟩
    rw [hNmap] at hh
    exact hh.2
  have habs := Subgroup.inf_pPrimeCore_map_le_of_supplement U M hUfactor
  have hUMle : U ⊓ M ≤ (pPrimeCore q U).map U.subtype ⊔ (U ⊓ Lc) := by
    rw [hUM, hfactor, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro x ⟨m, hm, rfl⟩
      exact Subgroup.mem_sup_left (habs ⟨hMN ⟨m.property, hNG m hm.2⟩, ⟨m, hm.1, rfl⟩⟩)
    · rintro x ⟨m, hm, rfl⟩
      refine Subgroup.mem_sup_right ⟨hMN ⟨m.property, hNG m hm.2⟩, ?_⟩
      obtain ⟨b, hb, hbm⟩ := hm.1
      exact ⟨(b : G), hb, congrArg Subtype.val hbm⟩
  refine ⟨c, ⟨hccommon, c.property⟩, le_antisymm ?_ ?_⟩
  · calc
      U = (pPrimeCore q U).map U.subtype ⊔ (U ⊓ M) := hUfactor
      _ ≤ (pPrimeCore q U).map U.subtype ⊔ (U ⊓ Lc) := sup_le le_sup_left hUMle
  · exact sup_le (Subgroup.map_subtype_le _) inf_le_left


end Glauberman
