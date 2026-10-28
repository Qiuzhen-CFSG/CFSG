module
public import Theory.GroupTheory.PairedInvolutiveExtension
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
/-!
# Equal outer parity in the paired binary linear action

An outer automorphism on each component is an inner pair followed by the
simultaneous diagram action. A factor interchange whose square is inner has
equal outer parity on the two coordinate maps: unequal parity would make its
square outer. These formulas place the original source generators in the two
cosets used by the paired-extension recognition theorem without assuming that
the generators themselves are involutions.

Source: Aschbacher--Smith 2.4.34, printed p.548, manuscript of 1 March 2004.
-/

public section
namespace Matrix.PSL3Two.PairedActionParity
open MarkedAutomorphisms Theory.GroupTheory.PairedInvolutiveExtension
private theorem outer_coset_ne_inner {G : Type*} [Group G] (δ : MulAut G)
    (hout : ∀ g:G,δ≠MulAut.conj g) (g h : G) :
    MulAut.conj g * δ ≠ MulAut.conj h := by
  intro he
  apply hout (g⁻¹*h)
  calc
    δ=(MulAut.conj g)⁻¹*MulAut.conj h := by rw [←he]; group
    _=MulAut.conj (g⁻¹*h) := by rw [map_mul,map_inv]
private theorem outer_inner_product {G : Type*} [Group G] (δ : MulAut G) (g h : G) :
    (MulAut.conj g * δ) * MulAut.conj h = MulAut.conj (g*δ h) * δ := by
  ext x : 1
  change g*δ (h*x*h⁻¹)*g⁻¹=(g*δ h)*δ x*(g*δ h)⁻¹
  simp only [map_mul,map_inv]
  group

/-- Two outer factor actions occupy the simultaneous diagram coset. -/
theorem outer_pair_normal_form (a b : MulAut SL)
    (ha : ∀ g:SL,a≠MulAut.conj g) (hb : ∀ g:SL,b≠MulAut.conj g) :
    ∃ c d : SL, a.prodCongr b = MulAut.conj (c,d) * diagram.prodCongr diagram := by
  obtain ⟨c,hc|hc⟩ := inner_or_graph a
  · exact (ha c hc).elim
  obtain ⟨d,hd|hd⟩ := inner_or_graph b
  · exact (hb d hd).elim
  refine ⟨c,d,?_⟩
  rw [hc,hd]
  ext x : 1
  rfl

/-- A factor interchange whose square is inner has equal outer parity on its
coordinate maps. Its coset is the interchange or diagram-interchange coset. -/
theorem swapped_square_inner_normal_form (a b : MulAut SL) (u v : SL)
    (hsq : (a.prodCongr b * (MulEquiv.prodComm : MulAut (SL×SL)))^2=MulAut.conj (u,v)) :
    ∃ c d : SL, ∃ p : Bit,
      a.prodCongr b * (MulEquiv.prodComm : MulAut (SL×SL)) =
        MulAut.conj (c,d) * action diagram diagram_involutive (p,on) := by
  have hab : a*b=MulAut.conj u := by
    ext x : 1
    exact congrArg Prod.fst (MulEquiv.congr_fun hsq (x,1))
  obtain ⟨c,hc|hc⟩ := inner_or_graph a <;> obtain ⟨d,hd|hd⟩ := inner_or_graph b
  · refine ⟨c,d,1,?_⟩
    rw [hc,hd]
    ext x : 1
    simp [action,MulEquiv.prodCongr]
    rfl
  · exfalso
    apply outer_coset_ne_inner diagram diagram_ne_conj (c*d) u
    simpa only [hc,hd,map_mul,mul_assoc] using hab
  · exfalso
    apply outer_coset_ne_inner diagram diagram_ne_conj (c*diagram d) u
    rw [hc,hd,outer_inner_product] at hab
    exact hab
  · refine ⟨c,d,on,?_⟩
    rw [hc,hd]
    ext x : 1
    simp [action,MulEquiv.prodCongr]
    rfl
end Matrix.PSL3Two.PairedActionParity
