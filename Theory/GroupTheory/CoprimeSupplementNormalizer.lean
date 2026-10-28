module
public import Theory.GroupTheory.PCoreSupplementQuotient
public import Theory.GroupTheory.PerfectSmallNormalizer

/-!
# Coprime normalizers of prime-core supplements

Suppose R supplements O_p(J) in a finite local group J. If a subgroup K of order prime
to p normalizes R, then K intersect J lies in R. The index of R in
J divides the order of O_p(J); normalization makes the relative index
of R in K intersect J divide that same index. Coprimeness forces it to
be one. Neither R nor K is assumed normal in J, and the ambient group
need not be finite.

Source application: DGS, Groups and Graphs (1985), (14.3)(b), p.212.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
variable {J R K : Subgroup G} [Finite J]
/-- The actual intersection with the local group lies in the supplement. -/
theorem coprime_normalizer_inf_le_pCore_supplement (hRJ : R ≤ J) (hcover : R ⊔ J.pCoreIn p=J)
    (hn : K ≤ normalizer (R : Set G))
    (hcop : Nat.Coprime p (Nat.card K)) : K ⊓ J ≤ R := by
  let Rj := R.subgroupOf J
  let Kj := K.subgroupOf J
  let N := pCore p J
  have hgen : Rj ⊔ N = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRJ,←MonoidHom.range_eq_map,range_subtype]
    exact hcover
  have hn' : Kj ≤ normalizer (Rj : Set J) := by
    intro x hx
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp (hn hx) y)
  have hi : Rj.index ∣ Nat.card N := by
    rw [←relIndex_top_right,←hgen,sup_comm,relIndex_sup_of_normal_left N Rj]
    exact relIndex_dvd_card Rj N
  have hk : Rj.relIndex Kj ∣ Rj.index := by
    let E := Rj ⊔ Kj
    let _ : (Rj.subgroupOf E).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le Rj.le_normalizer hn')
    have he := relIndex_sup_right (Kj.subgroupOf E) (Rj.subgroupOf E)
    rw [←subgroupOf_sup le_sup_right le_sup_left,sup_comm Kj Rj,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_right] at he
    rw [←he]
    exact relIndex_dvd_index_of_le le_sup_left
  have hcard : Nat.card Kj ∣ Nat.card K := by
    let j : Kj →* K := (J.subtype.comp Kj.subtype).codRestrict K (fun x => x.property)
    exact card_dvd_of_injective j (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : K => (z:G)) he)))
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := p) (G := J)).exists_card_eq
  have hc : Nat.Coprime (Nat.card N) (Nat.card Kj) := by
    rw [show Nat.card N=p^n from hn]
    exact (hcop.of_dvd_right hcard).pow_left n
  have hle : Kj ≤ Rj := relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hc (hk.trans hi) (relIndex_dvd_card Rj Kj))
  intro x hx
  exact hle (show (⟨x,hx.2⟩ : J)∈Kj from hx.1)
end Theory.GroupTheory
