module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.PlanePosition
public import Theory.GroupTheory.NormalFourCentralizerSeparation
/-!
# Sylow control for the original reflected cubic line

Every square in the original dihedral eight lies in the marked line, and
its rotation squares to z. Hence every normalizer fixes z. The order72
local normalizer therefore promotes this actual eight to a Sylow subgroup
of the global line normalizer by the normalizer-index congruence.

Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem cubicSylow_normalizer_le_centralizer (R:RootPair z) (h:IsType z) (X:Subgroup G) (hX:Nat.card X=9)
    (hXH:X≤centralizer z) (m:CubicNormalizer.ReflectedMarking z X)
    (ht:m.t∈R.cubicSylow X) (hs:m.s∈R.cubicSylow X) :
    normalizer (R.cubicSylow X:Set G)≤centralizer z := by
  intro g hg
  let r:=m.s*m.t
  have hr:r∈R.cubicSylow X := (R.cubicSylow X).mul_mem hs ht
  have hgr:g*r*g⁻¹∈R.cubicSylow X := (mem_normalizer_iff.mp hg r).mp hr
  have hh:=R.cubicSylow_square_mem_line h X hX hXH (g*r*g⁻¹) hgr
  have he:(g*r*g⁻¹)^2=g*z*g⁻¹ := by
    calc
      (g*r*g⁻¹)^2=g*r^2*g⁻¹  := by simp only [pow_two]; group
      _=g*z*g⁻¹ := by rw [m.rotation_square]
  rw [he] at hh
  have hz:z≠1 := by intro hz; have hc:=h.involution; simp [hz] at hc
  have hgz:g*z*g⁻¹≠1 := by
    intro he
    apply hz
    have he':(MulAut.conj g) z=(MulAut.conj g) 1 := by simpa using he
    exact (MulAut.conj g).injective he'
  obtain ⟨a,ha,huniq⟩:=(Nat.card_eq_two_iff' (1:zpowers z)).mp (by rw [Nat.card_zpowers,h.involution])
  have hez:g*z*g⁻¹=z := congrArg Subtype.val
    ((huniq ⟨_,hh⟩ (fun he=>hgz (congrArg Subtype.val he))).trans
      (huniq ⟨z,mem_zpowers z⟩ (fun he=>hz (congrArg Subtype.val he))).symm)
  apply mem_centralizer_singleton_iff.mpr
  symm
  calc
    z*g=(g*z*g⁻¹)*g := by rw [hez]
    _=g*z := by group

theorem cubicSylow_not_dvd_line_index (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
        centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)) :
    ¬2∣(R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let T:=R.cubicSylow X
  let L:=centralizer z⊓normalizer (U:Set G)
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  have hTL:T≤L := by
    change R.cubicSylow X≤centralizer z⊓normalizer (U:Set G)
    rw [hlocal]
    exact le_inf (inf_le_left.trans R.T_le_centralizer) inf_le_right
  have hcard:Nat.card T=8:=R.cubicSylow_card h X hX hXH
  have hLc:Nat.card L=72 := by
    change Nat.card (centralizer z⊓normalizer (U:Set G):Subgroup G)=72
    rw [hlocal]
    exact h.cubic_local_normalizer_card X hX hXH
  have hi:¬2∣T.relIndex L := by
    have hc:=card_mul_index (T.subgroupOf L)
    rw [Nat.card_congr (subgroupOfEquivOfLe hTL).toEquiv,hcard,hLc] at hc
    change 8*T.relIndex L=72 at hc
    have : T.relIndex L=9 := by omega
    rw [this]; decide
  exact not_dvd_relIndex_of_normalizer_inf_le T L (normalizer (U:Set G))
    (IsPGroup.of_card (n:=3) hcard) (hTL.trans inf_le_right) hi
    (le_inf (inf_le_left.trans (R.cubicSylow_normalizer_le_centralizer h X hX hXH m ht hs)) inf_le_right)
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
