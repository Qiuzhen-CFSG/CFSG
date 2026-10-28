module
public import Theory.GroupTheory.Commutator.CentralRow
public import Theory.GroupAction.PerfectFixedCover
public import Theory.GroupAction.SubgroupConjugation

/-!
# Fixed representatives for central commutators

Let Q be solvable and let an actor A of coprime order normalize Q and
centralize r in Q. If [r,Q] centralizes Q, commutation with r is a
homomorphism with kernel C_Q(r). Every A-fixed element of its image has
an A-fixed representative: the displacement of a lift is a cocycle in
the solvable coprime kernel, so the coprime cocycle theorem corrects it.

This is the fixed-lift step in the commutator argument of
Aschbacher--Smith 4.2.13, printed p.612. No surjectivity onto an externally
specified module is assumed or inferred.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup.CentralRow
variable {G : Type*} [Group G] [Finite G]

/-- A fixed central commutator has a fixed representative under a coprime actor. -/
theorem exists_fixed_commutator (Q A : Subgroup G) (r : Q)
    (hc : ⁅zpowers (r : G), Q⁆ ≤ centralizer (Q : Set G))
    (hn : A ≤ normalizer (Q : Set G))
    (hr : A ≤ centralizer ({(r : G)} : Set G))
    (hs : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card A) (Nat.card Q))
    (v : G) (hv : v ∈ ⁅zpowers (r : G), Q⁆)
    (hfix : v ∈ centralizer (A : Set G)) :
    ∃ s : G, s ∈ Q ∧ s ∈ centralizer (A : Set G) ∧ ⁅(r : G),s⁆ = v := by
  have hm : (⁅zpowers r,(⊤ : Subgroup Q)⁆ : Subgroup Q).map Q.subtype =
      ⁅zpowers (r : G),Q⁆ := by
    rw [map_commutator,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hcQ : ⁅zpowers r,(⊤ : Subgroup Q)⁆ ≤ center Q := by
    intro q hq
    exact mem_center_iff.mpr (fun s => Subtype.ext
      (hc (hm ▸ mem_map_of_mem Q.subtype hq) s s.property))
  let f := Q.subtype.comp (commutatorHom r hcQ)
  have hf : f.range = ⁅zpowers (r : G),Q⁆ := by
    rw [MonoidHom.range_comp,commutatorHom_range,hm]
  let _ := conjMulDistribMulActionOfLeNormalizer A Q hn
  have heq (a : A) (q : Q) : f (a • q) = (a : G) * f q * (a : G)⁻¹ := by
    change ⁅(r : G),(a : G) * q * (a : G)⁻¹⁆ =
      (a : G) * ⁅(r : G),(q : G)⁆ * (a : G)⁻¹
    have hrr : (MulAut.conj (a : G)) (r : G) = r := by
      change (a : G) * r * (a : G)⁻¹ = r
      rw [mem_centralizer_singleton_iff.mp (hr a.property),mul_inv_cancel_right]
    have he := map_commutatorElement (MulAut.conj (a : G)).toMonoidHom (r : G) (q : G)
    change (MulAut.conj (a : G)) ⁅(r : G),(q : G)⁆ =
      ⁅(MulAut.conj (a : G)) (r : G),(MulAut.conj (a : G)) (q : G)⁆ at he
    rw [hrr] at he
    exact he.symm
  let : IsInvariant A Q f.ker := ⟨fun a q => by
    change f q = 1 ↔ f (a • q) = 1
    rw [heq]
    constructor
    · intro h; rw [h]; simp
    · intro h
      have hh := congrArg (fun z : G => (a : G)⁻¹ * z * a) h
      simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one,one_mul] using hh⟩
  obtain ⟨q,hq⟩ := hf.symm ▸ hv
  have hsolv : Group.IsSolvable f.ker := by
    let := hs
    infer_instance
  obtain ⟨n,hns⟩ := Theory.GroupAction.exists_fixed_mul_of_solvable_coprime_displacement
    f.ker hsolv (hcop.of_dvd_right (card_subgroup_dvd_card f.ker)) q (fun a => by
      change f (q⁻¹ * (a • q)) = 1
      rw [map_mul,map_inv,heq,hq]
      rw [hfix a a.property]
      simp)
  refine ⟨((q * n : Q) : G),(q * n).property,?_,?_⟩
  · intro a ha
    have hh := congrArg (fun z : Q => (z : G)) (hns (⟨a,ha⟩ : A))
    change a * ((q * n : Q) : G) * a⁻¹ = ((q * n : Q) : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · change f (q * n) = v
    rw [map_mul,show f (n : Q) = 1 from n.property,mul_one,hq]
/-- If commutators with the full actor centralizer centralize S, so do
all actor-fixed elements of the central commutator image. -/
theorem fixed_commutator_le_centralizer (Q A S : Subgroup G) (r : Q)
    (hc : ⁅zpowers (r : G), Q⁆ ≤ centralizer (Q : Set G))
    (hn : A ≤ normalizer (Q : Set G))
    (hr : A ≤ centralizer ({(r : G)} : Set G))
    (hs : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card A) (Nat.card Q))
    (hS : ⁅zpowers (r : G),centralizer (A : Set G)⁆ ≤ centralizer (S : Set G)) :
    ⁅zpowers (r : G),Q⁆ ⊓ centralizer (A : Set G) ≤ centralizer (S : Set G) := by
  intro v hv
  obtain ⟨s,_,hsa,he⟩ := exists_fixed_commutator Q A r hc hn hr hs hcop v hv.1 hv.2
  rw [←he]
  exact hS (commutator_mem_commutator (mem_zpowers (r : G)) hsa)


omit [Finite G] in
/-- The literal commutator map into a specified central displacement subgroup. -/
@[expose] def subgroupHom (Q V : Subgroup G) (r : Q)
    (hcomm : ⁅zpowers (r : G),Q⁆ ≤ V) (hc : Q ≤ centralizer (V : Set G)) : Q →* V where
  toFun s := ⟨⁅(r : G),(s : G)⁆,hcomm (commutator_mem_commutator (mem_zpowers (r : G)) s.property)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := by
    apply Subtype.ext
    change ⁅(r : G),(s : G) * t⁆ = ⁅(r : G),(s : G)⁆ * ⁅(r : G),(t : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have he := (hc s.property) ⁅(r : G),(t : G)⁆
      (hcomm (commutator_mem_commutator (mem_zpowers (r : G)) t.property))
    calc
      _ = ⁅(r : G),(s : G)⁆ * ((s : G) * ⁅(r : G),(t : G)⁆) * (s : G)⁻¹ := by group
      _ = ⁅(r : G),(s : G)⁆ * ⁅(r : G),(t : G)⁆ := by rw [←he]; group

omit [Finite G] in
/-- The kernel is exactly the relative centralizer, with the original inclusion. -/
theorem subgroupHom_ker (Q V : Subgroup G) (r : Q)
    (hcomm : ⁅zpowers (r : G),Q⁆ ≤ V) (hc : Q ≤ centralizer (V : Set G)) :
    (subgroupHom Q V r hcomm hc).ker = (centralizer ({(r : G)} : Set G)).subgroupOf Q := by
  ext s
  change (⟨⁅(r : G),(s : G)⁆,_⟩ : V) = 1 ↔ (s : G) ∈ centralizer ({(r : G)} : Set G)
  rw [Subtype.ext_iff]
  change ⁅(r : G),(s : G)⁆ = 1 ↔ (s : G) ∈ centralizer ({(r : G)} : Set G)
  rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff]
  exact eq_comm

omit [Finite G] in
/-- The ambient image is the full commutator subgroup, rather than just a
subgroup of the module into which the displacement map was corestricted. -/
theorem subgroupHom_range_map (Q V : Subgroup G) (r : Q)
    (hcomm : ⁅zpowers (r : G),Q⁆ ≤ V) (hc : Q ≤ centralizer (V : Set G)) :
    (subgroupHom Q V r hcomm hc).range.map V.subtype = ⁅zpowers (r : G),Q⁆ := by
  have hm : (⁅zpowers r,(⊤ : Subgroup Q)⁆ : Subgroup Q).map Q.subtype =
      ⁅zpowers (r : G),Q⁆ := by
    rw [map_commutator,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hcQ : ⁅zpowers r,(⊤ : Subgroup Q)⁆ ≤ center Q := by
    intro q hq
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext ((hc s.property) _ (hcomm (hm ▸ mem_map_of_mem Q.subtype hq))).symm
  have he : V.subtype.comp (subgroupHom Q V r hcomm hc) =
      Q.subtype.comp (commutatorHom r hcQ) := by ext s; rfl
  rw [←MonoidHom.range_comp,he,MonoidHom.range_comp,commutatorHom_range,hm]

end Subgroup.CentralRow
