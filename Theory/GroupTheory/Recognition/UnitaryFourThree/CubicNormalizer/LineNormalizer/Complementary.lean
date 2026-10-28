module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Data
/-!
# The two actual fixed lines and the index-three action

The two original reflections have disjoint fixed lines because their
rotation inverts X. Each line is preserved by N(X), and the canonical V
has index eight in N(X). Together with index24 in N(U), this supplies the
literal index-three coset action used in the source line mover.
Source: Aschbacher, Sporadic Groups (1994),45.7–45.8,pp.245–246.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem reflected_fixed_lines_span (h:IsType z) (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hB:Nat.card ((P:Subgroup (centralizer z)).map (centralizer z).subtype⊓Subgroup.centralizer ({m.s}:Set G):Subgroup G)=3) :
    (((P:Subgroup (centralizer z)).map (centralizer z).subtype⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G)⊔
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype⊓Subgroup.centralizer ({m.s}:Set G):Subgroup G))=
      (P:Subgroup (centralizer z)).map (centralizer z).subtype := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let B:=X⊓Subgroup.centralizer ({m.s}:Set G)
  let : IsElementaryAbelian 3 X:=h.toCentralizerHypothesis.nine_elementary X (h.cubic_sylow_image_card P) (map_subtype_le _)
  have hd:U⊓B=⊥:=by
    apply eq_bot_iff.mpr
    intro x hx
    have ht:m.t*x*m.t⁻¹=x:=mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.1.2).symm
    have hs:m.s*x*m.s⁻¹=x:=mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2.2).symm
    have hr:(m.s*m.t)*x*(m.s*m.t)⁻¹=x:=by
      calc
        _=m.s*(m.t*x*m.t⁻¹)*m.s⁻¹:=by group
        _=x:=by rw[ht,hs]
    have he:x=x⁻¹:=hr.symm.trans (m.rotation_inverts x hx.1.1)
    have h2:x^2=1:=by simpa only[pow_two] using (congrArg (x*·) he).trans (mul_inv_cancel x)
    have h3:x^3=1:=elemPow_eq_one_of_isElementaryAbelian x hx.1.1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)))
  have hnorm:B≤normalizer (U:Set G):=by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb u hu
    exact congrArg Subtype.val (mul_comm' (⟨u,hu.1⟩:X) (⟨b,hb.1⟩:X))
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes U B hnorm
  rw[m.common_fixed_card,hB,hd,card_bot,one_mul] at hc
  exact eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (by rw[h.cubic_sylow_image_card P,←hc])

theorem cubic_normalizer_preserves_reflected_line (h:IsType z) (P:Sylow 3 (centralizer z))
    (v:G) (hv:v∈centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)) :
    normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)≤
      normalizer ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({v}:Set G):Subgroup G):Set G) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let B:=X⊓Subgroup.centralizer ({v}:Set G)
  let V:=CubicNormalizer.oddKernel X
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  rw[h.toCentralizerHypothesis.cubic_normalizer_split X hX hXH]
  apply sup_le
  · apply le_trans ?_ (centralizer_le_normalizer _)
    exact (map_subtype_le _:V≤Subgroup.centralizer (X:Set G)).trans (centralizer_le (show (B:Set G)⊆X from inf_le_left))
  · rw[inf_comm]
    exact normalizes_fixed_of_square_centralizes (centralizer z⊓normalizer (X:Set G)) X inf_le_right
      (fun n hn=>h.cubic_normalizer_square_centralizes X hX hXH n ⟨hn.2,hn.1⟩) v hv

theorem cubic_normalizer_kernel_index (R:RootPair z) (h:IsType z) (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G))=8 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let T:=R.cubicSylow X
  have hXV:X≤V:=by rw[←h.toCentralizerHypothesis.cubic_oddKernel_fixed X (h.cubic_sylow_image_card P) (map_subtype_le _)];exact inf_le_left
  have he:normalizer (X:Set G)=V⊔T:=by
    rw[h.toCentralizerHypothesis.cubic_normalizer_split X (h.cubic_sylow_image_card P) (map_subtype_le _),inf_comm,
      R.cubic_local_normalizer_product h X (h.cubic_sylow_image_card P) (map_subtype_le _),←sup_assoc,sup_eq_left.mpr hXV]
  have hV:Nat.card V=81:=(h.reflected_kernel_of_source_binary_normalizers P m).2
  have hT:Nat.card T=8:=R.cubicSylow_card h X (h.cubic_sylow_image_card P) (map_subtype_le _)
  have hd:V⊓T=⊥:=(disjoint_of_coprime_natCard (by rw[hV,hT];decide)).eq_bot
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes V T
    (inf_le_right.trans (CubicNormalizer.normalizer_normalizes_oddKernel X))
  rw[hV,hT,hd,card_bot,one_mul,←he] at hc
  have hVN:V≤normalizer (X:Set G):=he ▸ le_sup_left
  have hi:=(V.subgroupOf (normalizer (X:Set G))).card_mul_index
  rw[Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv,hV,←hc] at hi
  change 81*V.relIndex (normalizer (X:Set G))=81*8 at hi
  exact Nat.eq_of_mul_eq_mul_left (by decide) hi
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
