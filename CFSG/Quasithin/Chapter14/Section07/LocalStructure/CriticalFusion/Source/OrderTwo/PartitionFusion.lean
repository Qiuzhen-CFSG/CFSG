module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Ambient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections

/-!
# The two final partition comparisons in 14.7.69

In rank three, the four-group E∩V avoids the single-commutator part. A
reciprocal partition puts it in the union of Vᵍ and U₀ᵍ. A subgroup covered
by two subgroups lies in one of them; fusion of V's nonidentity elements
excludes the second. Hyperplane uniqueness then gives Vᵍ=V, contradicting
V₁≰Uα. This argument does not need an element swapping the two endpoints.

In rank two, the same single-commutator part forces E∩U₀ into U₀ᵍ.
Its order is two, and its image modulo V₁ is fixed by T. The actual earlier
14.7.68(2) uniqueness gives U₀ᵍ=U₀. The point fusion in 14.7.68(1) recovers
N_G(U₀)=H, giving the contradiction.

These are conditional partition-comparison lemmas, not 14.7.69. Their
reciprocal partitions must be constructed by transport of the source setup.
The fusion premises are exactly the preceding 14.7.68 conclusions, owned
by qt-14-07-critical-residual-fusion. Source: Aschbacher–Smith, combined
manuscript of 1 March 2004, printed pp.1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

/-- The actual natural L-action fuses every nonidentity element of V to z. -/
theorem seed_isConj_point (x : G) (hx : x ∈ V) (hn : x ≠ 1) : IsConj d.z x := by
  let := d.natural.chosen.elementary
  have hcx : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hn
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨l, _, hl⟩ := d.natural.subspace_transitive (F.Vi 1) (zpowers x)
    (F.le_seed 1) (zpowers_le.mpr hx) (hp.trans hcx.symm)
  have hz : d.z ∈ F.Vi 1 := d.point ▸ mem_zpowers d.z
  have hzl : (MulAut.conj l⁻¹) d.z ∈ zpowers x :=
    hl ▸ mem_map_of_mem (MulAut.conj l⁻¹).toMonoidHom hz
  have hnz : (MulAut.conj l⁻¹) d.z ≠ 1 := by
    intro he
    exact d.z_ne_one ((MulAut.conj l⁻¹).injective (he.trans (map_one _).symm))
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : zpowers x)).mp hcx
  have he : (MulAut.conj l⁻¹) d.z = x := by
    have h1 := ha ⟨_, hzl⟩ (fun h => hnz (congrArg Subtype.val h))
    have h2 := ha ⟨x, mem_zpowers x⟩ (fun h => hn (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  exact isConj_iff.mpr ⟨l⁻¹, he⟩

/-- Point fusion controls V∩U₀ᵍ by the literal conjugate of V₁. -/
theorem seed_inf_conjugate_fixed_le_point
    (fusion : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z}) (g : G) :
    V ⊓ conjugate d.U₀ g ≤ conjugate (F.Vi 1) g := by
  intro x hx
  by_cases hn : x = 1
  · subst x
    exact one_mem _
  obtain ⟨y, hy, rfl⟩ := hx.2
  have hconj : IsConj d.z y :=
    (d.seed_isConj_point _ hx.1 hn).trans (isConj_iff.mpr ⟨g⁻¹, rfl⟩).symm
  have he : y = d.z := Set.mem_singleton_iff.mp (fusion ▸ And.intro hconj hy)
  subst y
  exact mem_map_of_mem _ (d.point ▸ mem_zpowers d.z)

private theorem normalizer_fixed_eq_of_fusion
    (fusion : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z}) :
    normalizer (d.U₀ : Set G) = F.H := by
  apply le_antisymm ?_ d.H_normalizes_U₀
  intro g hg
  have hz : (MulAut.conj g⁻¹) d.z ∈ d.U₀ :=
    (conjugate_eq_iff d.U₀ g).mpr hg ▸ mem_map_of_mem _ d.z_mem_U₀
  have he : (MulAut.conj g⁻¹) d.z = d.z := Set.mem_singleton_iff.mp
    (fusion ▸ And.intro (isConj_iff.mpr ⟨g⁻¹, rfl⟩) hz)
  have he' : g⁻¹ * d.z = d.z * g⁻¹ := by
    apply mul_inv_eq_iff_eq_mul.mp
    exact he
  rw [d.centralizer_eq, mem_centralizer_singleton_iff]
  simpa using (Commute.inv_left he').eq

namespace CriticalChart
variable {d} {hc : d.SectionCentralizer} {c : CriticalPath (L := L) F}
  (b : d.CriticalChart hc c)

/-- The apparent exclusions in the source definition of E₁ just remove
the identity commutator. This characterization is intrinsic to the two
ambient elementary abelian groups and can therefore be transported. -/
theorem ambientE₁_eq_nontrivial_commutators
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    b.ambientE₁ = {z : G | z ≠ 1 ∧ ∃ x ∈ c.Uα, ∃ y ∈ F.U, ⁅x, y⁆ = z} := by
  ext z
  constructor
  · intro hz
    refine ⟨fun he => b.one_not_mem_ambientE₁ h earlier sep localActors hUH (he ▸ hz), ?_⟩
    obtain ⟨x, hx, _, y, hy, _, he⟩ := hz
    exact ⟨x, hx, y, hy, he⟩
  · rintro ⟨hn, x, hx, y, hy, rfl⟩
    refine ⟨x, hx, ?_, y, hy, ?_, rfl⟩
    · intro hcore
      have hp : ⁅x, y⁆ ∈ F.Vi 1 := by
        rw [← hcomm, commutator_comm]
        exact commutator_mem_commutator hcore hy
      have hE := b.ambient_commutator_mem earlier hUH hx hy
      have hz : ⁅x, y⁆ ∈ b.ambientE ⊓ F.Vi 1 := ⟨hE, hp⟩
      rw [h.inf_eq_bot] at hz
      exact hn (mem_bot.mp hz)
    · intro hfixed
      have hm : CriticalIntersections.ModuleCalculations d c (c.Uα_le_H earlier) := by
        obtain ⟨hm, hf, hd⟩ := b.original_module_calculations earlier sep localActors
          (c.Uα_le_H earlier)
        exact ⟨hm, hf, hd⟩
      have he := (CriticalIntersections.centralizer_and_products d c
        (c.Uα_le_H earlier) hUH hm).2.2
      have hyc : y ∈ F.U ⊓ centralizer (c.Uα : Set G) := he.symm ▸ hfixed
      exact hn (commutatorElement_eq_one_iff_mul_comm.mpr (hyc.2 x hx))

/-- The same set has the reverse commutator description. Commutators lie
in the actual elementary abelian U, so inversion does not alter them. -/
theorem ambientE₁_eq_reverse_commutators
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    b.ambientE₁ = {z : G | z ≠ 1 ∧ ∃ y ∈ F.U, ∃ x ∈ c.Uα, ⁅y, x⁆ = z} := by
  let := d.U_elementary
  have hs (x : G) (hx : x ∈ c.Uα) (y : G) (hy : y ∈ F.U) : ⁅x, y⁆ = ⁅y, x⁆ := by
    have hm := b.ambient_commutator_mem earlier hUH hx hy
    have hp : ⁅x, y⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := F.U) ⁅x, y⁆ hm.1
    have hi : ⁅x, y⁆⁻¹ = ⁅x, y⁆ := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hp)
    exact hi.symm.trans (commutatorElement_inv x y)
  rw [b.ambientE₁_eq_nontrivial_commutators h earlier sep localActors hUH hcomm]
  ext z
  constructor
  · rintro ⟨hn, x, hx, y, hy, he⟩
    exact ⟨hn, y, hy, x, hx, (hs x hx y hy).symm.trans he⟩
  · rintro ⟨hn, y, hy, x, hx, he⟩
    exact ⟨hn, x, hx, y, hy, (hs x hx y hy).trans he⟩

/-- A genuine reciprocal path gives the same E₁ after its actual right
conjugation. The path may be different; g is not assumed to swap endpoints. -/
theorem ambientE₁_right_transport
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    {r : CriticalPath (L := L) F} (b' : d.CriticalChart hc r)
    (h' : b'.AmbientComplement) (earlier' : r.EarlierImages)
    (localActors' : b'.LocalActors) (hUH' : F.U ≤ conjugate F.H r.conjugator)
    (g : G) (hbase : conjugate F.U g = c.Uα) (htip : conjugate r.Uα g = F.U) :
    (MulAut.conj g⁻¹) '' b'.ambientE₁ = b.ambientE₁ := by
  rw [b'.ambientE₁_eq_nontrivial_commutators h' earlier' sep localActors' hUH' hcomm,
    b.ambientE₁_eq_reverse_commutators h earlier sep localActors hUH hcomm]
  ext z
  constructor
  · rintro ⟨v, ⟨hn, x, hx, y, hy, rfl⟩, rfl⟩
    refine ⟨fun he => hn ((MulAut.conj g⁻¹).injective (he.trans (map_one _).symm)),
      (MulAut.conj g⁻¹) x, ?_, (MulAut.conj g⁻¹) y, ?_, ?_⟩
    · exact htip ▸ mem_map_of_mem _ hx
    · exact hbase ▸ mem_map_of_mem _ hy
    · exact (map_commutatorElement (MulAut.conj g⁻¹) x y).symm
  · rintro ⟨hn, y, hy, x, hx, rfl⟩
    have hy' : y ∈ conjugate r.Uα g := htip.symm ▸ hy
    have hx' : x ∈ conjugate F.U g := hbase.symm ▸ hx
    obtain ⟨a, ha, rfl⟩ := hy'
    obtain ⟨a', ha', rfl⟩ := hx'
    refine ⟨⁅a, a'⁆, ⟨?_, a, ha, a', ha', rfl⟩,
      map_commutatorElement (MulAut.conj g⁻¹) a a'⟩
    intro he
    apply hn
    rw [← map_commutatorElement, he, map_one]

/-- Transport the whole marked three-part partition along the reciprocal
path, preserving the ambient intersection and the literal commutator set. -/
theorem rank_three_partition_right_transport
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    {r : CriticalPath (L := L) F} (b' : d.CriticalChart hc r)
    (h' : b'.AmbientComplement) (earlier' : r.EarlierImages)
    (localActors' : b'.LocalActors) (hUH' : F.U ≤ conjugate F.H r.conjugator)
    (g : G) (hbase : conjugate F.U g = c.Uα) (htip : conjugate r.Uα g = F.U) :
    (b.ambientE : Set G) =
      ((b.ambientE ⊓ conjugate V g : Subgroup G) : Set G) ∪
      ((b.ambientE ⊓ conjugate d.U₀ g : Subgroup G) : Set G) ∪ b.ambientE₁ := by
  have hE : conjugate b'.ambientE g = b.ambientE := by
    change conjugate (F.U ⊓ r.Uα) g = F.U ⊓ c.Uα
    rw [conjugate_inf, hbase, htip, inf_comm]
  have h0 : conjugate b'.ambientE₀ g = b.ambientE ⊓ conjugate d.U₀ g := by
    change conjugate (b'.ambientE ⊓ d.U₀) g = _
    rw [conjugate_inf, hE]
  have hV : conjugate b'.ambientEV g = b.ambientE ⊓ conjugate V g := by
    change conjugate (b'.ambientE ⊓ V) g = _
    rw [conjugate_inf, hE]
  have h1 := b.ambientE₁_right_transport h earlier sep localActors hUH hcomm
    b' h' earlier' localActors' hUH' g hbase htip
  have hp := congrArg (Set.image (MulAut.conj g⁻¹))
    (b'.ambient_rank_three_partition h' earlier' sep localActors' hUH')
  simp only [Set.image_union] at hp
  change (conjugate b'.ambientE g : Set G) =
    (conjugate b'.ambientE₀ g : Set G) ∪ (conjugate b'.ambientEV g : Set G) ∪
      (MulAut.conj g⁻¹) '' b'.ambientE₁ at hp
  rw [hE, h0, hV, h1] at hp
  exact hp.trans (congrArg (fun S : Set G => S ∪ b.ambientE₁) (Set.union_comm _ _))

/-- The two-part partition also transports through the one-dimensional
central quotient, on the same original U/V₁ and with the same E₁. -/
theorem rank_two_partition_right_transport
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) (hcard : Nat.card d.U₀ = 4)
    {r : CriticalPath (L := L) F} (b' : d.CriticalChart hc r)
    (h' : b'.AmbientComplement) (earlier' : r.EarlierImages)
    (localActors' : b'.LocalActors) (hUH' : F.U ≤ conjugate F.H r.conjugator)
    (g : G) (hbase : conjugate F.U g = c.Uα) (htip : conjugate r.Uα g = F.U) :
    (b.ambientE : Set G) =
      ((b.ambientE ⊓ conjugate d.U₀ g : Subgroup G) : Set G) ∪ b.ambientE₁ := by
  have hE : conjugate b'.ambientE g = b.ambientE := by
    change conjugate (F.U ⊓ r.Uα) g = F.U ⊓ c.Uα
    rw [conjugate_inf, hbase, htip, inf_comm]
  have h0 : conjugate b'.ambientE₀ g = b.ambientE ⊓ conjugate d.U₀ g := by
    change conjugate (b'.ambientE ⊓ d.U₀) g = _
    rw [conjugate_inf, hE]
  have h1 := b.ambientE₁_right_transport h earlier sep localActors hUH hcomm
    b' h' earlier' localActors' hUH' g hbase htip
  have hp := congrArg (Set.image (MulAut.conj g⁻¹))
    (b'.ambient_rank_two_partition h' earlier' sep localActors' hUH' hcard)
  simp only [Set.image_union] at hp
  change (conjugate b'.ambientE g : Set G) =
    (conjugate b'.ambientE₀ g : Set G) ∪ (MulAut.conj g⁻¹) '' b'.ambientE₁ at hp
  rwa [hE, h0, h1] at hp

/-- The smallest case needs only the two transported complement identities.
In particular it does not assume a reciprocal centralizer equality. -/
theorem rank_one_fusion_contradiction
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hpoint : ¬ F.Vi 1 ≤ c.Uα)
    (hcard : Nat.card d.U₀ = 2)
    {r : CriticalPath (L := L) F} (b' : d.CriticalChart hc r) (h' : b'.AmbientComplement)
    (g : G) (hbase : conjugate F.U g = c.Uα) (htip : conjugate r.Uα g = F.U) :
    False := by
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have h0 : d.U₀ = F.Vi 1 :=
    (eq_of_le_of_card_ge d.point_le_U₀ (by omega)).symm
  have hP : d.U₀ ⊔ V = V := sup_eq_right.mpr (h0.le.trans (F.le_seed 1))
  have hEV : b.ambientE ≤ V := le_sup_left.trans (h.sup_eq.trans hP).le
  have hEV' : b'.ambientE ≤ V := le_sup_left.trans (h'.sup_eq.trans hP).le
  have hE : conjugate b'.ambientE g = b.ambientE := by
    change conjugate (F.U ⊓ r.Uα) g = F.U ⊓ c.Uα
    rw [conjugate_inf, hbase, htip, inf_comm]
  have hEVg : b.ambientE ≤ conjugate V g := hE.ge.trans (map_mono hEV')
  have hEc : Nat.card b.ambientE = 4 := by
    rw [b.card_ambientE h earlier sep localActors, hcard]
  have hv := d.lemma_14_7_67_two sep b.ambientE hEV hEc g hEVg
  exact hpoint ((F.le_seed 1).trans
    (hv.ge.trans ((map_mono (Data.V_le_U F)).trans_eq hbase)))

/-- Rank-three fusion comparison with the reciprocal partition still explicit.
The marked conjugator sends U to Uα; no endpoint-swapping element is assumed. -/
theorem rank_three_fusion_contradiction
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hpoint : ¬ F.Vi 1 ≤ c.Uα) (hcard : Nat.card d.U₀ = 8)
    (fusion : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (g : G) (hgU : conjugate F.U g = c.Uα)
    (reverse : (b.ambientE : Set G) =
      ((b.ambientE ⊓ conjugate V g : Subgroup G) : Set G) ∪
      ((b.ambientE ⊓ conjugate d.U₀ g : Subgroup G) : Set G) ∪ b.ambientE₁) :
    False := by
  have hd := b.ambientE₁_disjoint_seed h earlier sep localActors hUH hcard
  have hcover : (b.ambientEV : Set G) ⊆
      (conjugate V g : Set G) ∪ (conjugate d.U₀ g : Set G) := by
    intro x hx
    have hm : x ∈ (b.ambientE : Set G) := hx.1
    rw [reverse] at hm
    rcases hm with (hv | hu) | h1
    · exact Or.inl hv.2
    · exact Or.inr hu.2
    · exact (Set.disjoint_left.mp hd h1 hx).elim
  have hEVg : b.ambientEV ≤ conjugate V g := by
    rcases SubgroupClass.subset_union.mp hcover with hv | hu
    · exact hv
    · have hp : b.ambientEV ≤ conjugate (F.Vi 1) g :=
        (le_inf inf_le_right hu).trans (d.seed_inf_conjugate_fixed_le_point fusion g)
      have hb := Nat.card_le_card_of_injective (Subgroup.inclusion hp)
        (Subgroup.inclusion_injective hp)
      have hpc : Nat.card (conjugate (F.Vi 1) g) = 2 := by
        rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
        simpa using F.card 1 (by decide)
      rw [b.card_ambientEV h earlier sep localActors, hpc] at hb
      omega
  have hv := d.lemma_14_7_67_two sep b.ambientEV inf_le_right
    (b.card_ambientEV h earlier sep localActors) g hEVg
  apply hpoint
  have hV : V ≤ c.Uα := by
    exact hv.ge.trans ((map_mono (Data.V_le_U F)).trans_eq hgU)
  exact (F.le_seed 1).trans hV

/-- Rank-two fusion comparison. The fixed-vector hypothesis in 14.7.68(2)
is proved from the same original projection, not supplied as an extra premise. -/
theorem rank_two_fusion_contradiction
    (h : b.AmbientComplement) (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hpoint : ¬ F.Vi 1 ≤ c.Uα) (hcard : Nat.card d.U₀ = 4)
    (fusion : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (unique : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      (∀ t : T, d.action ⟨t, F.invariant 1 t.property⟩
        (d.conjugationSection.coordinates u).toAdd =
          (d.conjugationSection.coordinates u).toAdd) →
      centralizer ({(u : G)} : Set G) ≤ F.H ∧
        ∀ g : G, (u : G) ∈ conjugate d.U₀ g → conjugate d.U₀ g = d.U₀)
    (g : G) (hgU : conjugate F.U g = c.Uα)
    (reverse : (b.ambientE : Set G) =
      ((b.ambientE ⊓ conjugate d.U₀ g : Subgroup G) : Set G) ∪ b.ambientE₁) :
    False := by
  have hd := b.ambientE₁_disjoint_central h earlier sep localActors hUH
  have h0g : b.ambientE₀ ≤ conjugate d.U₀ g := by
    intro x hx
    have hm : x ∈ (b.ambientE : Set G) := hx.1
    rw [reverse] at hm
    rcases hm with h0 | h1
    · exact h0.2
    · exact (Set.disjoint_left.mp hd h1 hx).elim
  have h0 : Nat.card b.ambientE₀ = 2 := by
    have hh := b.twice_card_ambientE₀ h earlier sep localActors
    omega
  have hnb : b.ambientE₀ ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨x, hn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnb
  have hx := x.property
  have hn' : (x : G) ≠ 1 := fun he => hn (Subtype.ext he)
  let u : F.U := ⟨x, hx.1.1⟩
  have hfix : ∀ t : T, d.action ⟨t, F.invariant 1 t.property⟩
      (d.conjugationSection.coordinates u).toAdd =
        (d.conjugationSection.coordinates u).toAdd := by
    intro t
    exact d.kernel_fixed_of_card_U₀_four hcard _ _ ((d.mem_U₀ u).mp hx.2)
  have he : conjugate d.U₀ g = d.U₀ := (unique u hx.2 hn' hfix).2 g (h0g hx)
  have hg : g ∈ F.H := by
    rw [← d.normalizer_fixed_eq_of_fusion fusion]
    exact (conjugate_eq_iff d.U₀ g).mp he
  have hU : conjugate F.U g = F.U :=
    (conjugate_eq_iff F.U g).mpr (d.conjugationSection.normalized hg)
  apply hpoint
  rw [← hgU, hU]
  exact d.conjugationSection.kernel_le

end CriticalChart
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
