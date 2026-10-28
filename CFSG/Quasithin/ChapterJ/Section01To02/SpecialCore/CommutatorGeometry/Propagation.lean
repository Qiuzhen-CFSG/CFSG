module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import Theory.Representation.PSL3Two.SteinbergStructure.LocalActions
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient

/-!
# Propagating the Sylow-fixed commutator seed in J.2.3

For W ≤ V, the elements of S whose commutators lie in W form a subgroup.
Its image under the actual Steinberg coordinates is a binary subspace,
stable under N_L(W). If W is proper and nontrivial, a Sylow subgroup of
its parabolic stabilizer fixes a nonzero vector in that image. A full-image
commutator seed for Sylow-fixed lifts therefore excludes every proper image.

The Steinberg fixed-vector theorem gives one nonzero fixed coset for every
Sylow subgroup of L. Centrality of V makes its commutator image independent
of the chosen lift, and Sylow conjugacy transports a single full-image seed
to all these cosets. The initial full-image seed and the natural parabolic
stabilizer fact remain explicit premises here; they are not inferred merely
from the existence of a fixed vector.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3(6), printed p.433 (PDF p.444).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry
variable {G : Type*} [Group G] {L V : Subgroup G} (r : RuOne L V)

/-- The natural-action fact used by the source parabolic argument. Its
proof is independent of the commutator seed. -/
def NaturalParabolics (L V : Subgroup G) : Prop :=
  ∀ W : Subgroup G, W ≤ V → W ≠ ⊥ → W ≠ V →
    ∃ P : Sylow 2 L, ∀ g ∈ (P : Subgroup L), (g : G) ∈ normalizer W

/-- Elements all of whose commutators are in W. -/
private def rowKernel (W : Subgroup G) : Subgroup (L.pCoreIn 2) :=
  ⨅ s : L.pCoreIn 2,
    W.comap ((L.pCoreIn 2).subtype.comp (ClassTwo.commutatorHom r.classTwo s))

private lemma mem_rowKernel (W : Subgroup G) (t : L.pCoreIn 2) :
    t ∈ rowKernel r W ↔ ∀ s : L.pCoreIn 2, ⁅(t : G), (s : G)⁆ ∈ W := by
  simp only [rowKernel, mem_iInf, mem_comap, MonoidHom.comp_apply]
  change (∀ s : L.pCoreIn 2, ⁅(s : G), (t : G)⁆ ∈ W) ↔ _
  simp only [← commutatorElement_inv (t : G), inv_mem_iff]

private lemma commutator_le_iff (W : Subgroup G) (t : L.pCoreIn 2) :
    ⁅zpowers (t : G), L.pCoreIn 2⁆ ≤ W ↔ t ∈ rowKernel r W := by
  rw [mem_rowKernel, ← RuOne.commutator_map t, ← ClassTwo.commutatorHom_range r.classTwo t]
  constructor
  · intro h s
    exact h (mem_map.mpr ⟨_, ⟨s, rfl⟩, rfl⟩)
  · rintro h x ⟨_, ⟨s, rfl⟩, rfl⟩
    exact h s

/-- The image of the commutator kernel in the actual Steinberg coordinates. -/
private def rowSpace (W : Subgroup G) : Submodule (ZMod 2) BinaryLinearThree.Steinberg :=
  AddSubgroup.toZModSubmodule 2
    ((rowKernel r W).map r.steinberg.coordinates).toAddSubgroup'

private lemma mem_rowSpace (W : Subgroup G) (v : BinaryLinearThree.Steinberg) :
    v ∈ rowSpace r W ↔ ∃ t : L.pCoreIn 2,
      ⁅zpowers (t : G), L.pCoreIn 2⁆ ≤ W ∧ (r.steinberg.coordinates t).toAdd = v := by
  change (∃ t, t ∈ rowKernel r W ∧ r.steinberg.coordinates t = Multiplicative.ofAdd v) ↔ _
  simp only [commutator_le_iff r]
  rfl

private lemma rowSpace_stable (W : Subgroup G) (g : L) (hg : (g : G) ∈ normalizer W)
    (v : BinaryLinearThree.Steinberg) (hv : v ∈ rowSpace r W) :
    BinaryLinearThree.S (r.quotientMap g) v ∈ rowSpace r W := by
  obtain ⟨t, ht, rfl⟩ := (mem_rowSpace r W v).mp hv
  let t' : L.pCoreIn 2 := ⟨g * t * (g : G)⁻¹,
    (mem_normalizer_iff.mp (r.steinberg.normalized g.property) t).mp t.property⟩
  refine (mem_rowSpace r W _).mpr ⟨t', ?_, r.steinberg.equivariant g t⟩
  apply (commutator_le_iff r W t').mpr
  apply (mem_rowKernel r W t').mpr
  intro s
  let s' : L.pCoreIn 2 := ⟨(g : G)⁻¹ * s * g,
    by simpa using (mem_normalizer_iff.mp
      (r.steinberg.normalized g⁻¹.property) s).mp s.property⟩
  have hh : ⁅(t : G), (s' : G)⁆ ∈ W :=
    (mem_rowKernel r W t).mp ((commutator_le_iff r W t).mp ht) s'
  have hconj := (mem_normalizer_iff.mp hg ⁅(t : G), (s' : G)⁆).mp hh
  convert hconj using 1
  dsimp [t', s']
  group


/-- A nonzero invariant part of the Steinberg quotient contains a Sylow-fixed lift. -/
private lemma fixed_lift_in_rowSpace (W : Subgroup G) (P : Sylow 2 L)
    (hP : ∀ g ∈ (P : Subgroup L), (g : G) ∈ normalizer W)
    (hW : rowSpace r W ≠ ⊥) :
    ∃ t : L.pCoreIn 2, (t : G) ∉ V ∧ ⁅zpowers (t : G), L.pCoreIn 2⁆ ≤ W ∧
      ∀ g ∈ (P : Subgroup L),
        BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates t).toAdd =
          (r.steinberg.coordinates t).toAdd := by
  let A : Subrepresentation ((BinaryLinearThree.S.comp r.quotientMap).comp
      (P : Subgroup L).subtype) := {
    toSubmodule := rowSpace r W
    apply_mem_toSubmodule := fun g v hv => rowSpace_stable r W g (hP g g.property) v hv }
  let : Nontrivial A := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨v, hv, hf⟩ :=
    BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
      A.toRepresentation P.isPGroup'
  obtain ⟨t, ht, he⟩ := (mem_rowSpace r W v).mp v.property
  refine ⟨t, ?_, ht, ?_⟩
  · intro htV
    have hz := (r.steinberg.coordinates_eq_one_iff t).mpr htV
    apply hv
    apply Subtype.ext
    change (v : BinaryLinearThree.Steinberg) = 0
    rw [← he, hz]
    rfl
  · intro g hg
    rw [he]
    exact congrArg Subtype.val (hf ⟨g,hg⟩)

/-- The source parabolic argument: full commutation on Sylow-fixed lifts
forces full commutation on every noncentral element of S. -/
theorem full_commutator_of_sylow_seed
    (hparabolic : ∀ W : Subgroup G, W ≤ V → W ≠ ⊥ → W ≠ V →
      ∃ P : Sylow 2 L, ∀ g ∈ (P : Subgroup L), (g : G) ∈ normalizer W)
    (hseed : ∀ (P : Sylow 2 L) (t : L.pCoreIn 2), (t : G) ∉ V →
      (∀ g ∈ (P : Subgroup L),
        BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates t).toAdd =
          (r.steinberg.coordinates t).toAdd) →
      ⁅zpowers (t : G), L.pCoreIn 2⁆ = V)
    (t : L.pCoreIn 2) (ht : (t : G) ∉ V) :
    ⁅zpowers (t : G), L.pCoreIn 2⁆ = V := by
  by_contra hproper
  let W := ⁅zpowers (t : G), L.pCoreIn 2⁆
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hcent := commutator_eq_bot_iff_le_centralizer.mp hbot (mem_zpowers (t : G))
    apply ht
    rw [← r.center_eq]
    refine mem_map.mpr ⟨t, ?_, rfl⟩
    exact mem_center_iff.mpr fun s => Subtype.ext (hcent s s.property)
  obtain ⟨P, hP⟩ := hparabolic W (r.commutator_le_V t) hWne hproper
  have hn : rowSpace r W ≠ ⊥ := by
    intro hbot
    have hm : (r.steinberg.coordinates t).toAdd ∈ rowSpace r W :=
      (mem_rowSpace r W _).mpr ⟨t, le_rfl, rfl⟩
    rw [hbot, Submodule.mem_bot] at hm
    exact ht ((r.steinberg.coordinates_eq_one_iff t).mp hm)
  obtain ⟨w, hw, hcomm, hfixed⟩ := fixed_lift_in_rowSpace r W P hP hn
  have he := hseed P w hw hfixed
  exact hproper (le_antisymm (r.commutator_le_V t) (he ▸ hcomm))


lemma commutator_eq_of_coordinates_eq (t u : L.pCoreIn 2)
    (h : r.steinberg.coordinates t = r.steinberg.coordinates u) :
    ⁅zpowers (t : G), L.pCoreIn 2⁆ = ⁅zpowers (u : G), L.pCoreIn 2⁆ := by
  have hc : t * u⁻¹ ∈ center (L.pCoreIn 2) := by
    have hv : ((t * u⁻¹ : L.pCoreIn 2) : G) ∈ V :=
      (r.steinberg.coordinates_eq_one_iff _).mp (by
        rw [map_mul, map_inv, h]
        exact mul_inv_cancel (r.steinberg.coordinates u))
    rw [← r.center_eq] at hv
    obtain ⟨v, hv, he⟩ := hv
    exact (Subtype.ext he : v = t * u⁻¹) ▸ hv
  have he (s : L.pCoreIn 2) : ⁅(t : G), (s : G)⁆ = ⁅(u : G), (s : G)⁆ := by
    have hz : ClassTwo.commutatorHom r.classTwo s (t * u⁻¹) = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact (mem_center_iff.mp hc s)
    rw [map_mul, map_inv, mul_inv_eq_one] at hz
    have hv := congrArg (fun x : L.pCoreIn 2 => ((x : G)⁻¹)) hz
    change ⁅(s : G), (t : G)⁆⁻¹ = ⁅(s : G), (u : G)⁆⁻¹ at hv
    simpa only [commutatorElement_inv] using hv
  apply le_antisymm
  · apply (commutator_le_iff r _ t).mpr
    apply (mem_rowKernel r _ t).mpr
    intro s
    rw [he s]
    exact commutator_mem_commutator (mem_zpowers _) s.property
  · apply (commutator_le_iff r _ u).mpr
    apply (mem_rowKernel r _ u).mpr
    intro s
    rw [← he s]
    exact commutator_mem_commutator (mem_zpowers _) s.property

variable [Finite G]

/-- There is only one nontrivial fixed coset for each actual Sylow of L. -/
lemma sylow_fixed_lift (P : Sylow 2 L) :
    ∃ u : L.pCoreIn 2, (u : G) ∉ V ∧
      (∀ g ∈ (P : Subgroup L),
        BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates u).toAdd =
          (r.steinberg.coordinates u).toAdd) ∧
      (∀ t : L.pCoreIn 2, (t : G) ∉ V →
        (∀ g ∈ (P : Subgroup L),
          BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates t).toAdd =
            (r.steinberg.coordinates t).toAdd) →
        r.steinberg.coordinates t = r.steinberg.coordinates u) := by
  let P' := P.mapSurjective r.quotient_surjective
  obtain ⟨m, hm, hstab, huniq⟩ :=
    BinaryLinearThree.SteinbergStructure.LocalActions.sylow_fixedVector P'
  obtain ⟨u, hu⟩ := r.steinberg.onto (Multiplicative.ofAdd m)
  refine ⟨u, ?_, ?_, ?_⟩
  · intro huV
    exact hm (hu.symm.trans ((r.steinberg.coordinates_eq_one_iff u).mpr huV))
  · intro g hg
    rw [hu]
    exact (hstab _).mpr (by
      change r.quotientMap g ∈ (P'.toSubgroup : Subgroup BinaryLinearThree.Group)
      rw [Sylow.coe_mapSurjective]
      exact mem_map.mpr ⟨g, hg, rfl⟩)
  · intro t ht hf
    apply Multiplicative.toAdd.injective
    rw [hu]
    apply huniq _ (fun hz => ht ((r.steinberg.coordinates_eq_one_iff t).mp hz))
    intro g hg
    change g ∈ (P'.toSubgroup : Subgroup BinaryLinearThree.Group) at hg
    rw [Sylow.coe_mapSurjective] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact hf a ha

/-- The full centralizer of a Sylow-fixed coset in the model is the actual
image of that Sylow, not merely a subgroup isomorphic to it. -/
lemma sylow_fixed_stabilizer (P : Sylow 2 L) (u : L.pCoreIn 2)
    (hu : (u : G) ∉ V)
    (hf : ∀ g ∈ (P : Subgroup L),
      BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates u).toAdd =
        (r.steinberg.coordinates u).toAdd) (g : L) :
    BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates u).toAdd =
      (r.steinberg.coordinates u).toAdd ↔
      r.quotientMap g ∈ (P : Subgroup L).map r.quotientMap := by
  apply BinaryLinearThree.SteinbergStructure.LocalActions.sylow_fixed_stabilizer
    (P.mapSurjective r.quotient_surjective)
    _ (fun hz => hu ((r.steinberg.coordinates_eq_one_iff u).mp hz))
  intro a ha
  change a ∈ ((P.mapSurjective r.quotient_surjective : Sylow 2 BinaryLinearThree.Group) : Subgroup _) at ha
  rw [Sylow.coe_mapSurjective] at ha
  obtain ⟨b,hb,rfl⟩ := ha
  exact hf b hb



/-- The source's full stabilizer in L: the kernel S of the marking is
contained in every Sylow, so no extra elements are lost in the quotient. -/
lemma sylow_fixed_stabilizer_in_L (P : Sylow 2 L) (u : L.pCoreIn 2)
    (hu : (u : G) ∉ V)
    (hf : ∀ g ∈ (P : Subgroup L),
      BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates u).toAdd =
        (r.steinberg.coordinates u).toAdd) (g : L) :
    BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates u).toAdd =
      (r.steinberg.coordinates u).toAdd ↔ g ∈ (P : Subgroup L) := by
  rw [sylow_fixed_stabilizer r P u hu hf g]
  change g ∈ ((P : Subgroup L).map r.quotientMap).comap r.quotientMap ↔ _
  have hk : r.quotientMap.ker ≤ (P : Subgroup L) := by
    intro a ha
    rw [r.quotient_kernel] at ha
    obtain ⟨b, hb, he⟩ := pCoreIn_le_sylow L P ha
    exact (Subtype.ext he : b = a) ▸ hb
  rw [comap_map_eq_self hk]

/-- One full-image lift at the chosen Sylow is the only commutator seed
needed by the source argument. -/
def SylowSeed (P : Sylow 2 L) : Prop :=
  ∃ u : L.pCoreIn 2, (u : G) ∉ V ∧
    (∀ g ∈ (P : Subgroup L),
      BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates u).toAdd =
        (r.steinberg.coordinates u).toAdd) ∧
    ⁅zpowers (u : G), L.pCoreIn 2⁆ = V

omit [Finite G] in
lemma SylowSeed.conjugate (P : Sylow 2 L) (h : SylowSeed r P) (g : L) :
    SylowSeed r (g • P) := by
  obtain ⟨u, hu, hfix, hfull⟩ := h
  let u' : L.pCoreIn 2 := ⟨g * u * (g : G)⁻¹,
    (mem_normalizer_iff.mp (r.steinberg.normalized g.property) u).mp u.property⟩
  have he : (r.steinberg.coordinates u').toAdd =
      BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates u).toAdd :=
    r.steinberg.equivariant g u
  refine ⟨u', ?_, ?_, ?_⟩
  · intro hv
    have hgV := r.natural.normalized g.property
    exact hu ((mem_normalizer_iff.mp hgV u).mpr hv)
  · intro a ha
    rw [Sylow.coe_subgroup_smul] at ha
    change a ∈ (P : Subgroup L).map (MulAut.conj g).toMonoidHom at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [he]
    change BinaryLinearThree.S (r.quotientMap (g * b * g⁻¹))
      (BinaryLinearThree.S (r.quotientMap g) _) = _
    simp only [map_mul, map_inv, Module.End.mul_apply,
      Representation.inv_self_apply, hfix b hb]
  · have hh := congrArg (fun A : Subgroup G => A.map (MulAut.conj (g : G)).toMonoidHom) hfull
    have hS : (L.pCoreIn 2).map (MulAut.conj (g : G)).toMonoidHom = L.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (r.steinberg.normalized g.property)
    have hV : V.map (MulAut.conj (g : G)).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (r.natural.normalized g.property)
    rw [map_commutator, MonoidHom.map_zpowers, hS, hV] at hh
    exact hh

/-- Sylow conjugacy and uniqueness of the nonzero fixed vector transport
the source's one seed to every fixed lift at every Sylow. -/
theorem SylowSeed.full_commutator (P₀ : Sylow 2 L) (h : SylowSeed r P₀)
    (P : Sylow 2 L) (t : L.pCoreIn 2) (ht : (t : G) ∉ V)
    (hf : ∀ g ∈ (P : Subgroup L),
      BinaryLinearThree.S (r.quotientMap g) (r.steinberg.coordinates t).toAdd =
        (r.steinberg.coordinates t).toAdd) :
    ⁅zpowers (t : G), L.pCoreIn 2⁆ = V := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq L P₀ P
  obtain ⟨u, hu, huf, hfull⟩ := SylowSeed.conjugate r P₀ h g
  obtain ⟨v, _, _, huniq⟩ := sylow_fixed_lift r (g • P₀)
  have he := (huniq t ht hf).trans (huniq u hu huf).symm
  exact (commutator_eq_of_coordinates_eq r t u he).trans hfull

/-- The complete propagation step of J.2.3(6), with just the chosen
Sylow seed and the preceding natural parabolic fact left explicit. -/
theorem full_commutator_of_one_seed
    (hparabolic : ∀ W : Subgroup G, W ≤ V → W ≠ ⊥ → W ≠ V →
      ∃ P : Sylow 2 L, ∀ g ∈ (P : Subgroup L), (g : G) ∈ normalizer W)
    (P : Sylow 2 L) (hseed : SylowSeed r P)
    (t : L.pCoreIn 2) (ht : (t : G) ∉ V) :
    ⁅zpowers (t : G), L.pCoreIn 2⁆ = V :=
  full_commutator_of_sylow_seed r hparabolic
    (SylowSeed.full_commutator r P hseed) t ht


end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry
