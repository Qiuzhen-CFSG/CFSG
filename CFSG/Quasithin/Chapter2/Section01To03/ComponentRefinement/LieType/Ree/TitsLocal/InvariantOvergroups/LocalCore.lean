module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.ComponentLocalCore
public import Theory.GroupTheory.PCoreCentralizerOvergroup

/-!
# Characteristic two for a component local overgroup

A local subgroup K of a component has its two-core contained in the core
of the overgroup generated with S, provided N_S(L) normalizes K. If the
inner projection of z belongs to that local core, z belongs to the
overgroup core as well. Its core centralizer then lies in C_G(z) ≤ M.
The characteristic-two intersection with M detects characteristic two
in the overgroup; z also witnesses nontriviality of its actual core.

These are general local steps for Aschbacher–Smith 2.3.9(7), printed p.526.
The model must supply the invariant subgroup and projection-core membership.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Containing z in the actual core supplies every HeOver clause. -/
theorem mem_HeOver_of_mem_core (h : LocalSetup H L M S z) (K : Subgroup G)
    (hSK : (S : Subgroup H).map H.subtype ≤ K) (hKH : K ≤ H)
    (hzcore : z ∈ K.pCoreIn 2) :
    K ∈ Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  let := h.finite
  let N := K ⊓ M
  have hNH : N ≤ H ⊓ M := inf_le_inf hKH le_rfl
  let f : ↥(H ⊓ M) →* H := Subgroup.inclusion inf_le_left
  have hf : (S : Subgroup H) ≤ f.range := by
    intro x hx
    exact ⟨⟨(x : G), x.property, h.sylow_le ⟨x, hx, rfl⟩⟩, rfl⟩
  let T : Sylow 2 ↥(H ⊓ M) := S.comapOfInjective f (Subgroup.inclusion_injective _) hf
  have hTN : (T : Subgroup ↥(H ⊓ M)) ≤ N.subgroupOf (H ⊓ M) := by
    intro x hx
    exact ⟨hSK ⟨f x, hx, rfl⟩, x.property.2⟩
  have hc := centralizer_pCore_le_of_sylow_le T (N.subgroupOf (H ⊓ M)) hTN
    (Chapter1.mem_He_iff.mp h.local_even)
  have hN := (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hNH)).mp hc
  have hNK : centralizer (pCore 2 (N.subgroupOf K) : Set (N.subgroupOf K)) ≤
      pCore 2 (N.subgroupOf K) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe inf_le_left)).mpr hN
  have hHe : K ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    apply centralizer_pCore_le_of_overgroup 2 (N.subgroupOf K) hNK
    intro x hx
    refine ⟨x.property, h.centralizer_le ?_⟩
    obtain ⟨v, hv, hvz⟩ := hzcore
    apply mem_centralizer_singleton_iff.mpr
    rw [← hvz]
    exact (congrArg Subtype.val (mem_centralizer_iff.mp hx v hv)).symm
  refine ⟨hHe, ?_, hSK⟩
  intro he
  have hz1 : z = 1 := mem_bot.mp (he ▸ hzcore)
  have hz := h.involution
  rw [hz1, orderOf_one] at hz
  exact (by decide : (1 : ℕ) ≠ 2) hz

/-- A core projection puts z in the core of the local overgroup,
including when S permutes the components. -/
theorem mem_core_of_projection_core (h : LocalSetup H L M S z) (K : Subgroup L) (t : L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    (hproj : IsConjugationProjection L z t) (ht : t ∈ K.pCoreIn 2) :
    z ∈ (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2 := by
  let := h.finite
  let A := (S : Subgroup H).map H.subtype
  let B := K.map L.subtype
  let V := B ⊔ A
  have htB : (t : G) ∈ B.pCoreIn 2 := by
    rw [← map_pCoreIn_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective) K]
    exact mem_map_of_mem L.subtype ht
  have htV : (t : G) ∈ V.pCoreIn 2 :=
    h.component.pCoreIn_le_local_adjoin_in 2 h.component_le (map_subtype_le _)
      (map_subtype_le _) hinv htB
  let tv : V := ⟨t, pCoreIn_le 2 V htV⟩
  let zv : V := ⟨z, (show A ≤ V from le_sup_right) h.mem_sylow⟩
  have htcore : tv ∈ pCore 2 V := by
    obtain ⟨u, hu, he⟩ := htV
    exact (show u = tv from Subtype.ext he) ▸ hu
  have hgen : B.subgroupOf V ⊔ A.subgroupOf V = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self V
  have hzp : IsPGroup 2 (zpowers zv) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.involution, pow_one])
  have hzcore := Theory.GroupTheory.mem_pCore_of_inner_on_generator 2
    (B.subgroupOf V) (A.subgroupOf V) hgen zv tv hzp htcore
    (by
      intro k hk
      obtain ⟨l, hl, he⟩ := hk
      apply Subtype.ext
      change z * (k : G) * z⁻¹ = (t : G) * (k : G) * (t : G)⁻¹
      change (l : G) = (k : G) at he
      rw [← he]
      exact hproj l)
    (by
      intro a ha
      exact Subtype.ext (h.central a ha))
  exact mem_map.mpr ⟨zv, hzcore, rfl⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
