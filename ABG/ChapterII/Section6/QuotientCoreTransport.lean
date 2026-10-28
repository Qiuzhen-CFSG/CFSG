module

public import ABG.ChapterII.Section6.Defs

/-!
# Sylow transport through the p-prime-core quotient

The image of `O_{p',p}(G)` in the quotient by `O_{p'}(G)` is the quotient
`p`-core. A Sylow subgroup of the former maps onto the latter. The final
theorem records the corresponding intersection identity for any subgroup whose
intersection with `O_{p',p}(G)` is that Sylow subgroup.
-/

namespace ABG

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
public theorem Op_pPrimeCore_map_eq_pCore :
    (Op_p'p p G).map (QuotientGroup.mk' (pPrimeCore p G)) =
      pCore p (G ⧸ pPrimeCore p G) := by
  dsimp [Op_p'p]
  simpa using
    (Subgroup.map_comap_eq_self_of_surjective
      (f := QuotientGroup.mk' (pPrimeCore p G))
      (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
      (H := pCore p (G ⧸ pPrimeCore p G)))

public theorem subgroup_intersection_map_pCore
    (R : Subgroup G) (S : Sylow p (Op_p'p p G))
    (hS : (S : Subgroup (Op_p'p p G)) =
      R.subgroupOf (Op_p'p p G)) :
    (R ⊓ Op_p'p p G).map (QuotientGroup.mk' (pPrimeCore p G)) =
      pCore p (G ⧸ pPrimeCore p G) := by
  let M := pPrimeCore p G
  let q := QuotientGroup.mk' M
  let L := Op_p'p p G
  let core := pCore p (G ⧸ M)
  have hLmap : L.map q = core := by
    simpa [L, core, M] using Op_pPrimeCore_map_eq_pCore (G := G) (p := p)
  let restricted : L →* core :=
    (q.comp L.subtype).codRestrict core (fun element => by
      have hm : q (element : G) ∈ L.map q :=
        Subgroup.mem_map.mpr ⟨element, element.property, rfl⟩
      exact hLmap ▸ hm)
  have hrestricted : Function.Surjective restricted := by
    intro element
    have hm : element.val ∈ L.map q := hLmap.symm ▸ element.property
    obtain ⟨x, hx, heq⟩ := hm
    exact ⟨⟨x, hx⟩, Subtype.ext heq⟩
  have htop : ((S.mapSurjective hrestricted) : Subgroup core) = ⊤ := by
    apply top_unique
    exact ((pCore_isPGroup (p := p) (G := G ⧸ M)).to_subgroup ⊤).le_sylow_of_normal _
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans_eq hLmap
  · intro element helement
    have hm : (⟨element, helement⟩ : core) ∈
        (S.mapSurjective hrestricted : Subgroup core) := by
      rw [htop]
      trivial
    obtain ⟨x, hx, heq⟩ := hm
    refine ⟨x.val, ⟨?_, x.property⟩, congrArg Subtype.val heq⟩
    have hxR : (x : L) ∈ R.subgroupOf L := hS ▸ hx
    exact hxR

end ABG
