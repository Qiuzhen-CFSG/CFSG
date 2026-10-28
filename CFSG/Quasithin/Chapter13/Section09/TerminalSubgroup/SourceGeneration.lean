module
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.SourceRecognition
/-!
# The two four-cores generate the actual terminal Sylow

The faithful second-coordinate projection bounds the terminal base by eight.
Two distinct four-groups therefore fill it. Their elementary images in D8 are
the two Klein four planes, whose union contains every involution. Internal
fusion in the two actual local A4 cores consequently discharges the complete
I.4.1 recognition interface, without choosing an unjustified coordinate factor.
Source: Aschbacher--Smith, proof of 13.9.1, printed p.974.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath TerminalSubgroup
private theorem elementary_dihedral_plane (E:Subgroup D8) (hE:IsElementaryAbelian 2 E)
    (hcard:Nat.card E=4) : ∃b,E=plane b := by
  suffices ∃b,E≤plane b by
    obtain ⟨b,hb⟩:=this
    exact ⟨b,eq_of_le_of_card_ge hb (by rw [card_plane,hcard])⟩
  by_cases ht:E≤plane true
  · exact ⟨true,ht⟩
  obtain ⟨x,hx,hxt⟩:=Set.not_subset.mp ht
  refine ⟨false,?_⟩
  intro y hy
  have hlocal:∀x y:D8,x^2=1→y^2=1→x*y=y*x→x∉plane true→y∈plane false:=by decide +kernel
  exact hlocal x y (elemPow_eq_one_of_isElementaryAbelian x hx)
    (elemPow_eq_one_of_isElementaryAbelian y hy)
    (congrArg Subtype.val (hE.is_comm.comm (⟨x,hx⟩:E) ⟨y,hy⟩)) hxt

private theorem dihedral_involution_covered (A B:Subgroup D8)
    (hA:IsElementaryAbelian 2 A) (hB:IsElementaryAbelian 2 B)
    (hcA:Nat.card A=4) (hcB:Nat.card B=4) (hne:A≠B)
    (x:D8) (hx:x^2=1) : x∈A∨x∈B := by
  obtain ⟨a,rfl⟩:=elementary_dihedral_plane A hA hcA
  obtain ⟨b,rfl⟩:=elementary_dihedral_plane B hB hcB
  cases a <;> cases b
  · exact (hne rfl).elim
  · exact (by decide : ∀x:D8,x^2=1→x∈plane false∨x∈plane true) x hx
  · exact (by decide : ∀x:D8,x^2=1→x∈plane true∨x∈plane false) x hx
  · exact (hne rfl).elim

variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The two distinct actual four-groups inside the terminal base fill its
order-eight Sylow; no assertion identifies it with a prescribed coordinate factor. -/
theorem terminal_sup_fours_card (A B:Subgroup G)
    (hAJ:A≤m.dihedralBase) (hBJ:B≤m.dihedralBase)
    (hAH:A≤terminal m.terminalFour) (hBH:B≤terminal m.terminalFour)
    (hcA:Nat.card A=4) (hcB:Nat.card B=4) (hne:A≠B) :
    Nat.card (A⊔B:Subgroup G)=8 := by
  have hcard:Nat.card (A⊔B:Subgroup G)≤8:=
    (card_le_of_le (le_inf (sup_le hAJ hBJ) (sup_le hAH hBH))).trans m.terminalBase_card_le
  have hdiv:4∣Nat.card (A⊔B:Subgroup G):=hcA ▸ card_dvd_of_le (show A≤A⊔B from le_sup_left)
  have hlow:4≤Nat.card (A⊔B:Subgroup G):=hcA ▸ card_le_of_le (show A≤A⊔B from le_sup_left)
  have hne4:Nat.card (A⊔B:Subgroup G)≠4 := by
    intro he
    exact hne ((eq_of_le_of_card_ge le_sup_left (by rw [he,hcA])).trans
      (eq_of_le_of_card_ge le_sup_right (by rw [he,hcB])).symm)
  omega

/-- Every terminal Sylow involution lies in one of its two actual elementary
four-groups. The only finite calculation is on the eight-element dihedral model. -/
theorem terminal_sup_fours_involution (A B:Subgroup G)
    (hAJ:A≤m.dihedralBase) (hBJ:B≤m.dihedralBase)
    (hAH:A≤terminal m.terminalFour) (hBH:B≤terminal m.terminalFour)
    (hA:IsElementaryAbelian 2 A) (hB:IsElementaryAbelian 2 B)
    (hcA:Nat.card A=4) (hcB:Nat.card B=4) (hne:A≠B)
    (x:G) (hx:x∈A⊔B) (ho:orderOf x=2) : x∈A∨x∈B := by
  let D:=A⊔B
  let e:D≃*D8:=m.terminalBaseDihedralEquiv D (sup_le hAJ hBJ) (sup_le hAH hBH)
    (m.terminal_sup_fours_card A B hAJ hBJ hAH hBH hcA hcB hne)
  let A0:=A.subgroupOf D
  let B0:=B.subgroupOf D
  have hAA:IsElementaryAbelian 2 A0:=hA.of_surjective (subgroupOfEquivOfLe (show A≤D from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show A≤D from le_sup_left)).symm.surjective
  have hBB:IsElementaryAbelian 2 B0:=hB.of_surjective (subgroupOfEquivOfLe (show B≤D from le_sup_right)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show B≤D from le_sup_right)).symm.surjective
  have ha4:Nat.card (A0.map e.toMonoidHom)=4 := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe (show A≤D from le_sup_left)).toEquiv,hcA]
  have hb4:Nat.card (B0.map e.toMonoidHom)=4 := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe (show B≤D from le_sup_right)).toEquiv,hcB]
  have hab:A0.map e.toMonoidHom≠B0.map e.toMonoidHom := by
    intro h
    have hh: A0=B0:=(map_injective e.injective) h
    apply hne
    have:=congrArg (fun U:Subgroup D=>U.map D.subtype) hh
    simpa only [A0,B0,map_subgroupOf_eq_of_le (show A≤D from le_sup_left),
      map_subgroupOf_eq_of_le (show B≤D from le_sup_right)] using this
  have hp:(e ⟨x,hx⟩)^2=1 := by
    rw [←map_pow]
    have he:(⟨x,hx⟩:D)^2=1:=Subtype.ext (by change x^2=1; simpa only [ho] using pow_orderOf_eq_one x)
    rw [he,map_one]
  rcases dihedral_involution_covered _ _ (hAA.map e.toMonoidHom) (hBB.map e.toMonoidHom)
    ha4 hb4 hab (e ⟨x,hx⟩) hp with ha|hb
  · have hh : (⟨x,hx⟩:D)∈A0 := (mem_map_iff_mem e.injective).mp ha
    exact Or.inl hh
  · have hh : (⟨x,hx⟩:D)∈B0 := (mem_map_iff_mem e.injective).mp hb
    exact Or.inr hh

/-- Two internally fused four-cores supply every input of the actual terminal
recognition theorem. -/
theorem terminal_psl3Two_of_two_four_cores {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (A B:Subgroup G) (hAJ:A≤m.dihedralBase) (hBJ:B≤m.dihedralBase)
    (hAH:A≤terminal m.terminalFour) (hBH:B≤terminal m.terminalFour)
    (hA:IsElementaryAbelian 2 A) (hB:IsElementaryAbelian 2 B)
    (hcA:Nat.card A=4) (hcB:Nat.card B=4) (hne:A≠B)
    (hz:m.t*m.z∈A) (hzB:m.t*m.z∈B)
    (hfA:∀x (hx:x∈A),orderOf x=2→IsConj (⟨x,hAH hx⟩:terminal m.terminalFour) ⟨m.t*m.z,hAH hz⟩)
    (hfB:∀x (hx:x∈B),orderOf x=2→IsConj (⟨x,hBH hx⟩:terminal m.terminalFour) ⟨m.t*m.z,hBH hzB⟩) :
    Nonempty (terminal m.terminalFour≃*Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      m.factor 1≤centralizer (terminal m.terminalFour:Set G) := by
  apply m.terminal_psl3Two_of_generated_base hG (A⊔B) (sup_le hAJ hBJ) (sup_le hAH hBH)
    (m.terminal_sup_fours_card A B hAJ hBJ hAH hBH hcA hcB hne) (mem_sup_left hz)
  intro x hx
  have ho:orderOf (x:G)=2:=(orderOf_coe x).trans hx
  rcases m.terminal_sup_fours_involution A B hAJ hBJ hAH hBH hA hB hcA hcB hne x x.property ho with ha|hb
  · exact hfA x ha ho
  · exact hfB x hb ho
end CFSG.Quasithin.Chapter13.Section09.Marking
