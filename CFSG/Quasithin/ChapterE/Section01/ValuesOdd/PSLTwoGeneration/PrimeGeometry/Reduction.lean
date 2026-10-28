module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels

/-!
# From concrete prime-field geometry to local E1 members

For a self-centralizing elementary actor and a trivial ambient two-core,
τ(T,A) is exactly A. A concrete local subgroup containing A therefore meets
the ambient tau condition. The placement theorem supplies the literal Sylow
intersection, while the independent odd-section calculation supplies E1 and
its intrinsic quotient-image rank. Together these give the published local
escape contract, first for maximal overgroups and then for every proper one.

The two inputs remain explicit: this reduction is not a proof of the missing
PSL₂/PGL₂ placement or intrinsic odd-section calculation.

Source: Aschbacher--Smith, E.1.1--2, E.1.5 and E.1.14(6), pp.209--210 and 214.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- With trivial two-core and a self-centralizing actor, the ambient tau
is exactly that actor. -/
theorem tau_eq_self_of_selfCentralizing (T : Sylow 2 G) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hcore : pCore 2 G = ⊥) (hcent : centralizer (A : Set G) = A) :
    tau (T : Subgroup G) A = A := by
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have hcomm := (mem_centralizerModulo_iff.mp hx).2 a ha
      rw [hcore, mem_bot] at hcomm
      exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
    rwa [hcent] at hxC
  · exact le_sup_left.trans (sup_pCore_le_tau T A hAT)

/-- Actual local placement and the intrinsic odd-section calculation supply
all E1 conditions, including the quotient-image rank. -/
theorem largeFamilyEscapeAt_of_concrete_geometry (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥)
    (hcent : ∀ A : Subgroup G, IsKleinFour A → centralizer (A : Set G) = A)
    (hodd : ∀ A H : Subgroup G, IsKleinFour A → A ≤ H →
      LocalModel A H → ECaseOdd A H)
    (hgeometry : ConcreteLocalGeometryAt T) : LargeFamilyEscapeAt T := by
  apply largeFamilyEscapeAt_of_maximal_escape T
  intro Ω hΩ hlarge M hM hTM hNM
  obtain ⟨A, hA, hAT, hfour, H, hAH, hSylow, hmodel, hHM⟩ :=
    hgeometry Ω hΩ hlarge M hM hTM hNM
  let : IsElementaryAbelian 2 A := hΩ.1 A hA
  have htau := tau_eq_self_of_selfCentralizing T A hAT hcore (hcent A hfour)
  have ho : ECaseOdd A H := hodd A H hfour hAH hmodel
  have hrank : Group.rank ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 1 := by
    obtain ⟨r, _, _, _, _, _, hr⟩ := ho
    exact hr
  refine ⟨A, hA, hAT, H, ?_, hHM⟩
  exact ⟨⟨inferInstance, hAT, hAH, (by rw [htau]; exact le_inf hAT hAH), hSylow, Or.inl ho⟩,
    Or.inl ⟨ho, hrank.le⟩⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry
