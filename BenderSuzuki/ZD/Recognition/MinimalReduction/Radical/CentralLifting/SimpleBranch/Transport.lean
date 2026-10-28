module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Reduction
public import BenderSuzuki.SE.Borel

/-!
# Ambient formulation of the full ZD structure with trivial odd core

When the distinguished set generates and the odd core is trivial, the ZD
conclusion is equivalent to its clauses stated directly in the ambient group.
The equivalences below transport the actual derived subgroup and its Borel.
Source: GLS4, Chapter 2, Theorem ZD(a–e), printed p. 21.
-/

noncomputable section
namespace BenderSuzuki.ZD.SimpleBranch
open Theory.GroupTheory PFAppendixIII

/-- The ambient form of the structural clauses when the odd core is trivial. -/
@[expose] public def AmbientConclusion {G : Type*} [Group G] [Finite G]
    (Z : Set G) (M : Subgroup G) : Prop :=
  ∃ u : G, u ∈ M ∧ u ^ 2 = 1 ∧
    commutator G ⊔ Subgroup.zpowers u = ⊤ ∧
    Disjoint (commutator G) (Subgroup.zpowers u) ∧
    (∀ x ∈ commutator G, ∀ v ∈ Subgroup.zpowers u, Commute x v) ∧
    IsSimpleBenderGroup (commutator G) ∧
    IsBorelSubgroup (M.subgroupOf (commutator G)) ∧
    ∀ z ∈ Z, u⁻¹ * z ∈ commutator G ∧ z ≠ u

private theorem map_derived {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

/-- The exact ambient reformulation; both generation clauses and odd-core
containment in the original interface are reconstructed in the reverse direction. -/
public theorem ambientConclusion_iff {G : Type*} [Group G] [Finite G]
    {Z : Set G} {M : Subgroup G} (hgen : Subgroup.closure Z = ⊤)
    (hodd : pPrimeCore 2 G = ⊥) :
    StructureConclusion Z M ↔ AmbientConclusion Z M := by
  let L := Subgroup.closure Z
  let e : L ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have he (x : L) : e x = (x : G) := rfl
  let O := pPrimeCore 2 L
  have hO : O = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_bot, pPrimeCore_map_iso, hodd]
  let Q := L ⧸ O
  let q : L →* Q := QuotientGroup.mk' O
  let f : Q ≃* G :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e
  have hf (x : L) : f (q x) = e x := rfl
  have hC := map_derived e
  have hX := map_derived f
  let X := commutator Q
  change X.map f.toMonoidHom = commutator G at hX
  let ef : X ≃* commutator G := (f.subgroupMap X).trans (MulEquiv.subgroupCongr hX)
  have hef (x : X) : (ef x : G) = f x := rfl
  have hB : (((M.comap L.subtype ⊓ commutator L).map q).subgroupOf X).map
      ef.toMonoidHom = M.subgroupOf (commutator G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
      change f (y : Q) ∈ M
      change q z = (y : Q) at hzy
      rw [← hzy, hf, he]
      exact hz.1
    · intro hx
      let z := e.symm (x : G)
      have hzC : z ∈ commutator L := by
        exact Subgroup.mem_map_equiv.mp (hC.symm ▸ x.property)
      have hzM : (z : G) ∈ M := by
        change e z ∈ M
        simpa only [z, e.apply_symm_apply] using (show (x : G) ∈ M from hx)
      have hzX : q z ∈ X := by
        have hx' : f (q z) ∈ commutator G := by
          rw [hf]; simpa only [z, e.apply_symm_apply] using x.property
        rw [← hX, Subgroup.mem_map_equiv] at hx'
        simpa only [f.symm_apply_apply] using hx'
      exact ⟨⟨q z, hzX⟩, ⟨z, ⟨hzM, hzC⟩, rfl⟩,
        Subtype.ext (by change f (q z) = (x : G); rw [hf]; exact e.apply_symm_apply _)⟩
  change (∃ u : L, (u : G) ∈ M ∧ u ^ 2 = 1 ∧
    commutator L ⊔ Subgroup.zpowers u = ⊤ ∧
    X ⊔ Subgroup.zpowers (q u) = ⊤ ∧
    Disjoint X (Subgroup.zpowers (q u)) ∧
    (∀ x ∈ X, ∀ v ∈ Subgroup.zpowers (q u), Commute x v) ∧
    IsSimpleBenderGroup X ∧ O ≤ M.comap L.subtype ⊓ commutator L ∧
    IsBorelSubgroup (((M.comap L.subtype ⊓ commutator L).map q).subgroupOf X) ∧
    (∀ z : L, (z : G) ∈ Z → (q u)⁻¹ * q z ∈ X ∧ q z ≠ q u)) ↔ _
  constructor
  · rintro ⟨u, huM, hu2, hgenL, _, hd, hc, hm, _, hb, hz⟩
    refine ⟨e u, huM, ?_, ?_, ?_, ?_, hm.map_mulEquiv ef, ?_, ?_⟩
    · simpa only [map_pow, map_one] using congrArg e hu2
    · have hh := congrArg (Subgroup.map e.toMonoidHom) hgenL
      simpa only [Subgroup.map_sup, hC, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hh
    · apply disjoint_iff.mpr
      have hh := congrArg (Subgroup.map f.toMonoidHom) (disjoint_iff.mp hd)
      simpa only [Subgroup.map_inf _ _ f.toMonoidHom f.injective, hX, MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom, hf, Subgroup.map_bot] using hh
    · intro x hx v hv
      have hx' : f.symm x ∈ X := Subgroup.mem_map_equiv.mp (hX.symm ▸ hx)
      have hv' : f.symm v ∈ Subgroup.zpowers (q u) := by
        apply Subgroup.mem_map_equiv.mp
        rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hf]
      simpa only [MulEquiv.coe_toMonoidHom, f.apply_symm_apply] using
        (hc _ hx' _ hv').map f.toMonoidHom
    · exact hB ▸ hb.map_mulEquiv ef
    · intro z hzZ
      obtain ⟨hzmem, hzne⟩ := hz (e.symm z) (by simpa only [← he, e.apply_symm_apply] using hzZ)
      constructor
      · have hh := Subgroup.mem_map_of_mem f.toMonoidHom hzmem
        rw [hX] at hh
        simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, hf, e.apply_symm_apply] using hh
      · intro hzu
        apply hzne
        apply f.injective
        simpa only [hf, e.apply_symm_apply] using hzu
  · rintro ⟨u, huM, hu2, hg, hd, hc, hm, hb, hz⟩
    let v := e.symm u
    have hv : e v = u := e.apply_symm_apply u
    have hp : (Subgroup.zpowers (q v)).map f.toMonoidHom = Subgroup.zpowers u := by
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hf, hv]
    refine ⟨v, ?_, ?_, ?_, ?_, ?_, ?_, hm.map_mulEquiv ef.symm, ?_, ?_, ?_⟩
    · change e v ∈ M
      rwa [hv]
    · apply e.injective
      simpa only [map_pow, map_one, hv] using hu2
    · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      simpa only [Subgroup.map_sup, hC, MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom, hv, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hg
    · apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      simpa only [Subgroup.map_sup, hX, hp,
        Subgroup.map_top_of_surjective f.toMonoidHom f.surjective] using hg
    · apply disjoint_iff.mpr
      apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      simpa only [Subgroup.map_inf _ _ f.toMonoidHom f.injective, hX, hp, Subgroup.map_bot] using disjoint_iff.mp hd
    · intro x hx w hw
      apply f.injective
      simpa only [map_mul] using
        (hc _ (hX ▸ Subgroup.mem_map_of_mem f.toMonoidHom hx)
          _ (hp ▸ Subgroup.mem_map_of_mem f.toMonoidHom hw)).eq
    · rw [hO]; exact bot_le
    · have hh := hb.map_mulEquiv ef.symm
      rw [← hB, Subgroup.map_map] at hh
      have hi : ef.symm.toMonoidHom.comp ef.toMonoidHom = MonoidHom.id X := by
        apply MonoidHom.ext
        intro x
        exact ef.symm_apply_apply x
      simpa only [hi, Subgroup.map_id] using hh
    · intro z hzZ
      obtain ⟨hzm, hzne⟩ := hz (e z) hzZ
      constructor
      · have hh : f ((q v)⁻¹ * q z) ∈ commutator G := by
          simpa only [map_mul, map_inv, hf, hv] using hzm
        rw [← hX, Subgroup.mem_map_equiv] at hh
        simpa only [f.symm_apply_apply] using hh
      · intro hh
        apply hzne
        have := congrArg f hh
        simpa only [hf, hv] using this

end BenderSuzuki.ZD.SimpleBranch
