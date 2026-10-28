module

public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Prime cores of direct products

Projecting a normal p-subgroup into either factor bounds it by that factor's
p-core. Conversely the product of the two cores is normal and is a p-group.
The embedded version keeps intrinsic cores of subgroups in their ambient
product, as needed for compatible local subgroup markings.
-/

public section
open Subgroup
namespace Subgroup
variable {G A : Type*} [Group G] [Group A] [Finite G] [Finite A]

private theorem isPGroup_product {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hA : IsPGroup p A) :
    IsPGroup p (G × A) := by
  obtain ⟨m, hm⟩ := hG.exists_card_eq
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  exact IsPGroup.of_card (n := m + n) (by rw [Nat.card_prod, hm, hn, pow_add])

/-- The prime core of a finite direct product is the product of the prime cores. -/
theorem pCore_prod (p : ℕ) [Fact p.Prime] :
    pCore p (G × A) = (pCore p G).prod (pCore p A) := by
  apply le_antisymm
  · apply le_prod_iff.mpr
    constructor
    · exact le_sSup ⟨(inferInstance : (pCore p (G × A)).Normal).map _
        (fun g => ⟨(g,1),rfl⟩), pCore_isPGroup.map _⟩
    · exact le_sSup ⟨(inferInstance : (pCore p (G × A)).Normal).map _
        (fun a => ⟨(1,a),rfl⟩), pCore_isPGroup.map _⟩
  · exact le_sSup ⟨inferInstance,
      (isPGroup_product pCore_isPGroup pCore_isPGroup).of_equiv
        (prodEquiv (pCore p G) (pCore p A)).symm⟩

/-- Intrinsic cores retain their ambient product coordinates. -/
theorem pCoreIn_prod (p : ℕ) [Fact p.Prime] (B : Subgroup G) (C : Subgroup A) :
    (B.prod C).pCoreIn p = (B.pCoreIn p).prod (C.pCoreIn p) := by
  let e := prodEquiv B C
  have he : (pCore p (B.prod C)).map e.toMonoidHom = (pCore p B).prod (pCore p C) :=
    (pCore_map_iso p e).trans (pCore_prod p)
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have h := mem_map_of_mem e.toMonoidHom hx
    rw [he] at h
    exact ⟨⟨⟨x.val.1,x.property.1⟩,h.1,rfl⟩,
      ⟨⟨x.val.2,x.property.2⟩,h.2,rfl⟩⟩
  · rintro ⟨⟨b,hb,hbz⟩,⟨c,hc,hcz⟩⟩
    refine ⟨⟨(b.val,c.val),b.property,c.property⟩,?_,Prod.ext hbz hcz⟩
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [he]
    exact ⟨hb,hc⟩

omit [Finite G] in
/-- A p-subgroup is its own intrinsic p-core. -/
theorem pCoreIn_eq_self_of_isPGroup (p : ℕ) (B : Subgroup G) (hB : IsPGroup p B) :
    B.pCoreIn p = B :=
  le_antisymm (pCoreIn_le p B) (le_pCoreIn_of_normalizes hB le_rfl B.le_normalizer)

end Subgroup
