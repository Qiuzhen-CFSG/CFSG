module
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Eight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
/-!
# Finite A6 residual enlargement

A residual subgroup containing a Sylow dihedral centralizer and fusing all
involutions into its distinguished central involution satisfies the same I.4.1
hypotheses. I.4.1 gives PSL3(2) or A6; divisibility excludes PSL3(2), while
A6's order forces the subgroup to be all of A6. This is the minimal local
recognition used in Aschbacher--Smith F.5.5, printed p.302.
-/
public noncomputable section
open Subgroup
namespace CFSG.Quasithin.DihedralInvolutionCentralizerHypotheses
variable {H:Type*} [Group H] [Finite H]

theorem subgroup_eq_top_of_sylow_involution_fusion
    (eH:H≃*alternatingGroup (Fin 6)) (S:Sylow 2 H)
    (eS:S≃*DihedralGroup 4) (z:H) (hz:orderOf z=2)
    (hc:centralizer ({z}:Set H)=(S:Subgroup H))
    (J:Subgroup H) (hSJ:(S:Subgroup H)≤J)
    (hf:∀x:S,orderOf x=2 → ∃g∈J,g*x.val*g⁻¹=z) : J=⊤ := by
  have hzS:z∈(S:Subgroup H):=hc ▸ mem_centralizer_singleton_iff.mpr rfl
  let zJ:J:=⟨z,hSJ hzS⟩
  let P:=S.subtype hSJ
  have hcent : centralizer ({zJ}:Set J)=(S:Subgroup H).subgroupOf J := by
    ext x
    have hh : x∈centralizer ({zJ}:Set J) ↔ x.val∈centralizer ({z}:Set H) := by
      simp only [mem_centralizer_singleton_iff]
      exact Subtype.ext_iff
    rw [hh,hc]
    rfl
  have hzJ:orderOf zJ=2 := (orderOf_coe zJ).symm.trans hz
  let hJ:DihedralInvolutionCentralizerHypotheses J 3:={
    two_le:=by decide
    z:=zJ
    involution:=⟨fun he=>by rw [he,orderOf_one] at hzJ;omega,
      by rw [←hzJ];exact pow_orderOf_eq_one _⟩
    involutions_conjugate:=by
      intro x hx
      have ho:orderOf x=2:=orderOf_eq_prime hx.2 hx.1
      have hp:IsPGroup 2 (zpowers x):=IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,ho,pow_one])
      obtain ⟨Q,hQ⟩:=hp.exists_le_sylow
      obtain ⟨g,hg⟩:=MulAction.exists_smul_eq J Q P
      have hyP : MulAut.conj g x∈(P:Subgroup J) := by
        rw [←hg]
        exact mem_map_of_mem _ (hQ (mem_zpowers x))
      let y:S:=⟨(MulAut.conj g x).val,hyP⟩
      have hy2:orderOf y=2:=(orderOf_coe y).symm.trans
        ((orderOf_coe (MulAut.conj g x)).trans (((MulAut.conj g).orderOf_eq x).trans ho))
      obtain ⟨a,ha,he⟩:=hf y hy2
      let aJ:J:=⟨a,ha⟩
      refine ⟨aJ*g,?_⟩
      apply Subtype.ext
      have hh : aJ*(MulAut.conj g x)*aJ⁻¹=zJ:=Subtype.ext he
      have := congrArg Subtype.val hh
      simpa only [MulAut.conj_apply,map_mul,map_inv,coe_mul,coe_inv,mul_inv_rev,mul_assoc] using this
    centralizer_equiv:=⟨(MulEquiv.subgroupCongr hcent).trans
      ((subgroupOfEquivOfLe hSJ).trans eS)⟩ }
  have hH:Nat.card H=360:=by rw [Nat.card_congr eH.toEquiv,nat_card_alternatingGroup,Nat.card_fin];decide
  rcases hJ.recognize_eight with he | he
  · obtain ⟨e⟩ := he
    have hd:=J.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_PSL,hH] at hd
    norm_num at hd
  · obtain ⟨e⟩ := he
    have hJc:Nat.card J=360:=by rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin];decide
    exact eq_top_of_card_eq J (hJc.trans hH.symm)
end CFSG.Quasithin.DihedralInvolutionCentralizerHypotheses
