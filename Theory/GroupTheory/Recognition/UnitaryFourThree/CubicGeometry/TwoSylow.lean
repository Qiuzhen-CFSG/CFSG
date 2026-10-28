module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Action
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# The original dihedral Sylow in the cubic-kernel normalizer

The original involution centralizer normalizes V exactly when it normalizes
X=C_V(z), so the local intersection has order72. Every square in the original
Tx lies in ⟨z⟩ and the reflected rotation squares to z; consequently N_G(Tx)
centralizes z. Local Sylow maximality promotes Tx to Sylow2 N_G(V), with
order8. Thus sixteen cannot divide that normalizer order.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p247.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_kernel_local_normalizer (P:Sylow 3 (centralizer z)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V:=CubicNormalizer.oddKernel X
    centralizer z⊓normalizer (V:Set G)=centralizer z⊓normalizer (X:Set G) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  have hx:V⊓centralizer z=X:=h.toCentralizerHypothesis.cubic_oddKernel_fixed X
    (h.cubic_sylow_image_card P) (map_subtype_le _)
  change centralizer z⊓normalizer (V:Set G)=centralizer z⊓normalizer (X:Set G)
  apply le_antisymm
  · apply le_inf inf_le_left
    rw [←hx]
    exact (le_inf inf_le_right (inf_le_left.trans (centralizer z).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  · exact le_inf inf_le_left (inf_le_right.trans (CubicNormalizer.normalizer_normalizes_oddKernel X))

include h in
theorem cubic_kernel_sylow_two (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    ∃S:Sylow 2 (normalizer (V:Set G)),Nat.card S=8 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let M:=normalizer (V:Set G)
  let L:=M⊓centralizer z
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  obtain ⟨R⟩:=h.exists_rootPair
  let U:=R.cubicSylow X
  have hUc:Nat.card U=8:=R.cubicSylow_card h X hX hXH
  have hUL:U≤L:=le_inf (inf_le_right.trans (CubicNormalizer.normalizer_normalizes_oddKernel X))
    (inf_le_left.trans R.T_le_centralizer)
  have hLc:Nat.card L=72:=by
    change Nat.card (M⊓centralizer z:Subgroup G)=72
    rw [inf_comm,h.cubic_kernel_local_normalizer P]
    exact h.cubic_local_normalizer_card X hX hXH
  obtain ⟨m,ht,hs,_,_⟩:=R.exists_reflected_marking h X hX hXH
  have hzU:z∈U:=by
    rw [←m.rotation_square]
    exact U.pow_mem (U.mul_mem hs ht) 2
  have hnorm:normalizer (U:Set G)≤centralizer z:=by
    intro g hg
    have hrg:g*(m.s*m.t)*g⁻¹∈U:=(mem_normalizer_iff.mp hg _).mp (U.mul_mem hs ht)
    have hsq:=R.cubicSylow_square_mem_line h X hX hXH _ hrg
    have he:(g*(m.s*m.t)*g⁻¹)^2=g*z*g⁻¹:=by
      simpa only [MulAut.conj_apply,m.rotation_square] using
        (map_pow (MulAut.conj g) (m.s*m.t) 2).symm
    rw [he] at hsq
    have hne:g*z*g⁻¹≠1:=by
      intro hh
      have hz1:z=1:=(MulAut.conj g).injective (by simpa only [map_one,MulAut.conj_apply] using hh)
      have ho:=h.involution
      simp [hz1] at ho
    have hz2:Nat.card (zpowers z)=2:=by rw [Nat.card_zpowers,h.involution]
    have hline:(g*z*g⁻¹)=z:=by
      obtain ⟨a,ha,hall⟩:=(Nat.card_eq_two_iff' (1:zpowers z)).mp hz2
      have hzn:(⟨z,mem_zpowers z⟩:zpowers z)≠1:=by
        intro hh
        have ho:=h.involution
        simp only [show z=1 from congrArg Subtype.val hh,orderOf_one] at ho
        omega
      have hgn:(⟨g*z*g⁻¹,hsq⟩:zpowers z)≠1:=fun hh=>hne (congrArg Subtype.val hh)
      exact congrArg Subtype.val ((hall _ hgn).trans (hall _ hzn).symm)
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hline)
  have hi:¬2∣U.relIndex L:=by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup G) U L bot_le hUL
    simp only [relIndex_bot_left,hUc,hLc] at hh
    have he:U.relIndex L=9:=by omega
    rw [he];decide
  have hp:IsPGroup 2 U:=IsPGroup.of_card (n:=3) hUc
  have hglobal:=not_dvd_relIndex_of_normalizer_inf_le U L M hp (hUL.trans inf_le_left) hi
    (le_inf inf_le_right (inf_le_left.trans hnorm))
  let S:Sylow 2 M:=(hp.comap_subtype:IsPGroup 2 (U.subgroupOf M)).toSylow hglobal
  exact ⟨S,(Nat.card_congr (subgroupOfEquivOfLe (hUL.trans inf_le_left)).toEquiv).trans hUc⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_kernel_normalizer_not_sixteen (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    ¬16∣Nat.card (normalizer (V:Set G)) := by
  dsimp only
  obtain ⟨S,hS⟩:=h.cubic_kernel_sylow_two P
  have hh:=S.toSubgroup.card_mul_index
  rw [hS] at hh
  intro hd
  have he:2∣S.toSubgroup.index:=by
    apply (Nat.mul_dvd_mul_iff_left (by decide:0<8)).mp
    simpa only [hh] using hd
  exact S.not_dvd_index he
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
