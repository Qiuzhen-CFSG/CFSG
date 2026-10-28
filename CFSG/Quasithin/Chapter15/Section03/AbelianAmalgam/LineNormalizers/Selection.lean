module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Constructions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineChoice
public import Theory.GroupTheory.SylowNormalizerConjugate

/-!
# The Sylow adjustment of the escaping singular line

The weak-closure rank `r(G,V)=2` supplies an escaping four-group in `V`.
Conjugate it inside `M` so that its normalizer intersects the fixed Sylow
subgroup in a Sylow subgroup of its normalizer in `M`. Conjugation preserves
the order, the actual Klein-four isomorphism, containment in `V`, and escape
from `M`. The intersection conclusion of 15.3.46(2) then gives total
singularity of the adjusted subgroup.

The output contains an actual Sylow subgroup of `M_E` whose ambient image
is the prescribed `T_E`; no Sylow or terminal-normalizer conclusion is
assumed. The only chapter inputs are the earlier natural action,
`M=N_G(V)`, the singular-intersection conclusion, and the explicit rank.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the choice
immediately before Lemma 15.3.66, printed p.1152, PDF p.1169.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam

open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The source choice of `E`, including the Sylow adjustment inside `M`. -/
theorem exists_singular_escaping_four_with_sylow_lineT
    (T : Sylow 2 G) (V M : Subgroup G) [IsElementaryAbelian 2 V]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hTM : (T : Subgroup G) ≤ M)
    (hcardV : Nat.card V = 16) (hM : M = normalizer (V : Set G))
    (hr : ChapterE.globalR V = 2)
    (hsingular : ∀ g : G, g ∉ M →
      ∀ x : ↥(V ⊓ V.map (MulAut.conj g).toMonoidHom),
        d.singular ⟨x, x.property.1⟩) :
    ∃ (E : Subgroup G) (hEV : E ≤ V), Nat.card E = 4 ∧
      Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
      ¬ lineNormalizer E ≤ M ∧
      (∀ e : E, d.singular ⟨e, hEV e.property⟩) ∧
      ∃ P : Sylow 2 (lineM M E),
        (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E := by
  obtain ⟨E, hEV, hcard, ⟨equiv⟩, hescape, _⟩ :=
    exists_singular_escaping_four_of_globalR_eq_two V M d hcardV hM hr hsingular
  obtain ⟨m, hm, hi⟩ := T.exists_conjugate_normalizer_not_dvd_relIndex M E hTM
  let c := MulAut.conj m
  let E' := E.map c.toMonoidHom
  have hV : V.map c.toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizes hm)
  have hEV' : E' ≤ V := (map_mono hEV).trans_eq hV
  have hescape' : ¬ lineNormalizer E' ≤ M := by
    intro hN
    apply hescape
    intro n hn
    have hn' : c n ∈ lineNormalizer E' := by
      rw [show lineNormalizer E' = (lineNormalizer E).map c.toMonoidHom from
        (map_equiv_normalizer_eq E c).symm]
      exact mem_map_of_mem _ hn
    have hmem := M.mul_mem (M.mul_mem (M.inv_mem hm) (hN hn')) hm
    simpa [c, MulAut.conj_apply, mul_assoc] using hmem
  have hTE : lineT T E' ≤ lineM M E' := le_inf (inf_le_left.trans hTM) inf_le_right
  have hp : IsPGroup 2 (lineT T E') := T.isPGroup'.to_le inf_le_left
  have hi' : ¬ 2 ∣ (lineT T E').relIndex (lineM M E') := by
    have he : (lineT T E').subgroupOf (lineM M E') =
        (T : Subgroup G).subgroupOf (lineM M E') := by
      ext x
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.property.2⟩⟩
    rw [relIndex, he]
    exact hi
  refine ⟨E', hEV', ?_, ?_, hescape', ?_, ?_⟩
  · exact (card_map_of_injective c.injective).trans hcard
  · exact ⟨(E.equivMapOfInjective c.toMonoidHom c.injective).symm.trans equiv⟩
  · obtain ⟨g, hg, hgM⟩ := SetLike.not_le_iff_exists.mp hescape'
    have hEg : E'.map (MulAut.conj g).toMonoidHom = E' :=
      mem_normalizer_iff_map_conj_eq.mp hg
    have hEVg : E' ≤ V.map (MulAut.conj g).toMonoidHom := by
      rw [← hEg]
      exact map_mono hEV'
    intro e
    exact hsingular g hgM ⟨e, hEV' e.property, hEVg e.property⟩
  · exact ⟨(hp.comap_subtype (K := lineM M E')).toSylow hi',
      map_subgroupOf_eq_of_le hTE⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
