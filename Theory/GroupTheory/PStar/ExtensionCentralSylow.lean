module

public import Theory.GroupTheory.PStar.ExtensionKernels
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Mathlib.GroupTheory.Transfer

/-!
# Extensions with a central Sylow subgroup in the kernel

Transfer makes the residual of a group with central Sylow p-subgroup
prime to p. Factor this residual out of a kernel with central Sylow
subgroup. The remaining kernel is a central p-group, so the central and
coprime extension results apply in succession.

For a Sylow subgroup P of a normal subgroup N, every p-subgroup of
N intersect C_G(P) lies in P, by Sylow maximality. Thus the kernel of the
map from O^p(C_G(P)) onto G/N has central Sylow subgroup. This proves
GLS II, Chapter B, Lemma 5.4 from the two kernel cases of Lemma 5.3.
-/

public section
open Subgroup
namespace Subgroup
variable {p : ℕ} {G : Type*} [Group G] [Finite G] [Fact p.Prime]

/-- Transfer makes the residual prime to p when a Sylow subgroup is central. -/
theorem coprime_card_pResidual_of_central_sylow (P : Sylow p G)
    (hc : (P : Subgroup G) ≤ center G) : Nat.Coprime p (Nat.card (pResidual p G)) := by
  have hn : normalizer (P : Set G) ≤ centralizer (P : Set G) := by
    change normalizer ((P : Subgroup G) : Set G) ≤ centralizer ((P : Subgroup G) : Set G)
    rw [centralizer_eq_top_iff_subset.mpr hc]
    exact le_top
  let t := MonoidHom.transferSylow P hn
  have hR : pResidual p G ≤ t.ker := sInf_le ⟨inferInstance,
    (P.isPGroup'.to_subgroup t.range).of_equiv
      (QuotientGroup.quotientKerEquivRange t).symm⟩
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (MonoidHom.not_dvd_card_ker_transferSylow P hn)).of_dvd_right (card_dvd_of_le hR)

omit [Finite G] [Fact p.Prime] in
/-- A p-subgroup in N centralizing a Sylow subgroup of N lies in that Sylow. -/
theorem le_embedded_sylow_of_centralizes (N Q : Subgroup G) (P : Sylow p N)
    (hp : IsPGroup p Q) (hQN : Q ≤ N)
    (hc : Q ≤ centralizer ((P : Subgroup N).map N.subtype : Set G)) :
    Q ≤ (P : Subgroup N).map N.subtype := by
  have hc' : Q.subgroupOf N ≤ centralizer (P : Set N) := by
    intro q hq a ha
    exact Subtype.ext (hc hq a (mem_map_of_mem N.subtype ha))
  have hn : (P : Subgroup N) ≤ normalizer (Q.subgroupOf N : Set N) :=
    (le_centralizer_iff.mp hc').trans (centralizer_le_normalizer _)
  have hle := (hp.comap_subtype (K := N)).le_sylow_of_normalized P hn
  intro q hq
  exact mem_map.mpr ⟨⟨q, hQN hq⟩, hle hq, rfl⟩
end Subgroup

namespace Theory.GroupTheory
variable {p : ℕ} {G H : Type*} [Group G] [Group H] [Finite G] [Fact p.Prime]

/-- The central-Sylow kernel extension criterion. -/
theorem isPStar_of_surjective_central_sylow_kernel (hG : IsPPerfect p G)
    (f : G →* H) (hf : Function.Surjective f) (P : Sylow p f.ker)
    (hc : (P : Subgroup f.ker).map f.ker.subtype ≤ center G)
    (hH : IsPStar p H) : IsPStar p G := by
  let N := f.ker
  let R := (pResidual p N).map N.subtype
  let q := QuotientGroup.mk' R
  have hRN : R ≤ N := map_subtype_le _
  have hcN : (P : Subgroup N) ≤ center N := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc (mem_map_of_mem N.subtype hx)) y)
  have hRcop : Nat.Coprime p (Nat.card R) := by
    rw [Nat.card_congr ((pResidual p N).equivMapOfInjective N.subtype N.subtype_injective).symm.toEquiv]
    exact coprime_card_pResidual_of_central_sylow P hcN
  let fbar := QuotientGroup.lift R f hRN
  have hfbar : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective R f hf hRN
  have hNP : N.map q = ((P : Subgroup N).map N.subtype).map q := by
    have h := congrArg (Subgroup.map N.subtype) (pResidual_sup_sylow_eq_top P)
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
    have h' := congrArg (Subgroup.map q) h
    change (R ⊔ (P : Subgroup N).map N.subtype).map q = N.map q at h'
    simpa only [Subgroup.map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq] using h'.symm
  have hk : fbar.ker = ((P : Subgroup N).map N.subtype).map q :=
    (QuotientGroup.ker_lift R f hRN).trans hNP
  have hcentral : fbar.ker ≤ center (G ⧸ R) := by
    rw [hk]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective R y
    exact (map_mul q z x).symm.trans ((congrArg q (mem_center_iff.mp (hc hx) z)).trans
      (map_mul q x z))
  have hp : IsPGroup p fbar.ker := hk.symm ▸ ((P.isPGroup'.map N.subtype).map q)
  have hbar : IsPStar p (G ⧸ R) := isPStar_of_surjective_central_pgroup_kernel
    (hG.of_surjective q (QuotientGroup.mk'_surjective R)) fbar hfbar hcentral hp hH
  exact isPStar_of_surjective_coprime_kernel q (QuotientGroup.mk'_surjective R)
    (by simpa only [q, QuotientGroup.ker_mk'] using hRcop) hbar

/-- The residual of a Sylow centralizer is p-star if that centralizer
supplements the normal subgroup and the quotient is p-star. This is the
centralizer step in GLS II 5.3 and the implication used in 5.4. -/
theorem isPStar_pResidual_centralizer_of_quotient
    (N : Subgroup G) [N.Normal] (P : Sylow p N)
    (hquot : IsPStar p (G ⧸ N))
    (hgen : N ⊔ centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    IsPStar p (pResidual p (centralizer ((P : Subgroup N).map N.subtype : Set G))) := by
  let S := (P : Subgroup N).map N.subtype
  let C := centralizer (S : Set G)
  let R := pResidual p C
  let i : R →* G := C.subtype.comp R.subtype
  let q := QuotientGroup.mk' N
  let f : R →* G ⧸ N := q.comp i
  have hf : Function.Surjective f := by
    let g := q.comp C.subtype
    have hg : Function.Surjective g := by
      apply MonoidHom.range_eq_top.mp
      have h := congrArg (Subgroup.map q) hgen
      simpa only [g, q, MonoidHom.range_comp, range_subtype, Subgroup.map_sup,
        QuotientGroup.map_mk'_self, bot_sup_eq,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using h
    apply MonoidHom.range_eq_top.mp
    have hr := (map_pResidual_of_surjective p g hg).trans hquot.1
    simpa only [f, i, g, MonoidHom.range_comp, range_subtype, map_map] using hr
  let T : Sylow p f.ker := Sylow.nonempty.some
  let U := (T : Subgroup f.ker).map f.ker.subtype
  have hUN : U.map i ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (map_subtype_le _ hx)
  have hUC : U.map i ≤ centralizer (S : Set G) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.val.property
  have hUP : U.map i ≤ S := le_embedded_sylow_of_centralizes N (U.map i) P
    ((T.isPGroup'.map f.ker.subtype).map i) hUN hUC
  have hcentral : U ≤ center R := by
    intro x hx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (y.val.property (i x) (hUP (mem_map_of_mem i hx))).symm
  exact isPStar_of_surjective_central_sylow_kernel (isPPerfect_pResidual p)
    f hf T hcentral hquot

/-- The residual of the Sylow centralizer of a normal subgroup of a p-star
group is p-star (GLS II 5.4). -/
theorem IsPStar.isPStar_pResidual_centralizer (hG : IsPStar p G)
    (N : Subgroup G) [N.Normal] (P : Sylow p N) :
    IsPStar p (pResidual p (centralizer ((P : Subgroup N).map N.subtype : Set G))) :=
  isPStar_pResidual_centralizer_of_quotient N P (hG.quotient N) (hG.2 N P)

end Theory.GroupTheory
