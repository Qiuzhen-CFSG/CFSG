module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Alignment
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.OddQuotient

/-!
# The quotient-automorphism contradiction in local ZD

Let D be the derived subgroup of the distinguished closure in C_G(u).
Choose an involution t in D fixed by a commuting conjugate of u, and use
strong embedding to put t in M. Then z = ut is distinguished and commutes
with that adjusted conjugate w. Lemma 4.7 makes wz a product of distinguished
involutions, so product disconnection puts C_D(wz) in M.

The odd-core quotient action of w is outer by the four-group obstruction.
The fixed subgroup for wz lies in the actual Borel image of M, so that
action is inner. Since u centralizes D and z = ut, the actions of w and wz
differ by the inner automorphism induced by t. This is the contradiction.

Source: GLS, Volume 4, Chapter 2, Proposition 4.4, final paragraph.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- The final contradiction in GLS Proposition 4.4, retaining the odd core
and the actual quotient conjugation action. -/
public theorem local_centralizer_structure_false
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u v : G}
    (h : IsProductDisconnected Z M) (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (hC : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) ∧ z ∈ M)
    (huL : u ∈ centralizerClosure Z u)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype))
    (huv : u ≠ v) (hconj : IsConj u v) (hcomm : Commute u v) : False := by
  let L := centralizerClosure Z u
  let D := (commutator L).map L.subtype
  have hDC : D ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro x ⟨y, _, rfl⟩
    exact centralizerClosure_le Z u y.property
  have hCN := centralizer_le_local_derived_normalizer h u
  obtain ⟨hmodel, _, hB, hSE⟩ := LocalDerivedQuotient.local_derived_data Z M u hs
  obtain ⟨w, t, hw, huw, huwc, huwc', ht, htM, htw⟩ :=
    exists_aligned_commuting_conjugate hu huv hconj hcomm hDC
      (hCN (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm.eq)) hSE
  have hwN : w ∈ Subgroup.normalizer (D : Set G) :=
    hCN (Subgroup.mem_centralizer_singleton_iff.mpr huwc'.symm.eq)
  let nw : Subgroup.normalizer (D : Set G) := ⟨w, hwN⟩
  have hnw : nw ^ 2 = 1 := Subtype.ext hw.sq_eq_one
  have houter := bender_quotient_normalizer_outer D nw hnw hmodel
    (local_centralizer_not_twoRank_of_structure h hu huM hC hne huL hs huw huwc huwc')
  obtain ⟨hcoset, _⟩ := LocalCosetIdentification.local_obstruction_inputs_of_structure
    h hu huM hC hne huL hs
  have htG := BenderSuzuki.IsInvolution.map_of_injective ht D.subtype D.subtype_injective
  let z : G := u * (t : G)
  have hz : z ∈ Z := hcoset _ t.property htG
  have hzM : z ∈ M := M.mul_mem huM htM
  have hzw : Commute z w := huwc'.mul_left htw
  have hwM : w ∈ M := h.centralizer_le hz hzM
    (Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm.eq)
  have huZ := (not_mem_or_product_of_centralizer_not_le h hu huM hC).1
  have hwZ : w ∉ Z := by
    intro hwZ
    obtain ⟨g, hg⟩ := isConj_iff.mp huwc.symm
    have hh := h.invariant g w hwZ
    apply huZ
    simpa only [MulAut.conj_apply, hg] using hh
  have hwz : PFAppendixIII.IsInvolution (w * z) := by
    refine ⟨?_, ?_⟩
    · intro heq
      have hh := congrArg (fun x => x * z) heq
      have hwz' : w = z := by
        simpa only [mul_assoc, ← pow_two, (h.involutions z hz).sq_eq_one,
          mul_one, one_mul] using hh
      exact hwZ (hwz' ▸ hz)
    · rw [hzw.symm.mul_pow, hw.sq_eq_one, (h.involutions z hz).sq_eq_one, one_mul]
  obtain ⟨a, ha, b, hb, _, hab⟩ :=
    local_conjugate_distinguished_product h hu huM hC hne huL hs huwc hz hzw
  have hCM : Subgroup.centralizer ({w * z} : Set G) ≤ M := by
    have hh := h.product_centralizer a ha b hb (hab ▸ hwz) (hab ▸ M.mul_mem hwM hzM)
    rwa [← hab] at hh
  have huN : u ∈ Subgroup.normalizer (D : Set G) :=
    hCN (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  let nu : Subgroup.normalizer (D : Set G) := ⟨u, huN⟩
  let nt : Subgroup.normalizer (D : Set G) := ⟨t, Subgroup.le_normalizer t.property⟩
  let nz := nu * nt
  have hnwz : (nw * nz) ^ 2 = 1 := Subtype.ext hwz.sq_eq_one
  have hinner := bender_quotient_normalizer_inner D M (nw * nz) hnwz hmodel hB
    (inf_le_right.trans hCM)
  let O := pPrimeCore 2 D
  let q := QuotientGroup.mk' O
  let rho := O.quotientAut.comp D.normalizerMonoidHom
  have hrhou : rho nu = 1 := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h d =>
      change O.quotientAut (D.normalizerMonoidHom nu) (q d) = q d
      rw [Subgroup.quotientAut_apply_mk]
      congr 1
      apply Subtype.ext
      change u * (d : G) * u⁻¹ = (d : G)
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hDC d.property), mul_inv_cancel_right]
  have hrhot : rho nt = MulAut.conj (q t) := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h d =>
      change O.quotientAut (D.normalizerMonoidHom nt) (q d) = MulAut.conj (q t) (q d)
      rw [Subgroup.quotientAut_apply_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hrhoz : rho nz = MulAut.conj (q t) := by
    rw [show nz = nu * nt from rfl, map_mul, hrhou, one_mul, hrhot]
  have hinner' : ∃ b : D ⧸ O, rho nw * MulAut.conj (q t) = MulAut.conj b := by
    change ∃ b : D ⧸ O, rho (nw * nz) = MulAut.conj b at hinner
    simpa only [map_mul, hrhoz] using hinner
  exact houter ((MulAut.mul_conj_inner_iff (rho nw) (q t)).mp hinner')

end BenderSuzuki.ZD
