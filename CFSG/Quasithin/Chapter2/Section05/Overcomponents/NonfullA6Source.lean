module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6Terminal
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.A6QuotientSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.Exchanged
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.BinaryFixed
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.SymplecticFixed
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HSLocalSetup
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HSFixed
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.CoreFour

/-!
# Componenthood in the nonfull A₆ source branches

For the original Mathieu source setup, every involution of O₂(H) retains K
as a component of its centralizer when H/O₂(H) is M₁₀ or PGL₂(9).

A hypothetical larger component first gives the actual marked fixed A₆.
The complete quotient census leaves A₈, PSL₅(2), Sp₄(4), and HS. The binary
and symplectic rows give an S₆ fixed group. In the HS row the original
core-four Sylow geometry and nonfusion remove the central cover; its fixed
group then contains an S₆ overgroup of the original perfect component.
Each such S₆ contradicts the literal quotient H/O₂(H), using its order and
an element of order eight. All marks and subgroup maps are those of the
original source setup.

Source: Aschbacher–Smith 2.5.21, printed p.566, with the overcomponent
analysis of 2.5.19, printed pp.560–563.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Overcomponents Overcomponents.NonfullA6

/-- Every original two-core involution preserves the A₆ component in the
two nonfull outer-quotient branches. -/
theorem MathieuSourceSetup.nonfull_a6_core_involution_component
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hQ : Nonempty ((H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F))
    (i : G) (hiC : i ∈ twoCore H) (hi : orderOf i = 2) :
    IsComponentIn K (centralizer ({i} : Set G)) := by
  classical
  let Y := (S : Subgroup H).map H.subtype
  let eKH := (subgroupOfEquivOfLe c.component_le).trans eK
  let : (K.subgroupOf H).Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) _ eKH c.component
  obtain ⟨t, _, ht, _, htC, hline, _⟩ :=
    MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t ∈ centerIn Y := by
    have hh : t ∈ centerIn Y ⊓ twoCore H := hline.symm ▸ mem_zpowers t
    exact hh.1
  by_cases hti : t = i
  · subst i
    exact source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  have hcore := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hiYK : i ∈ Y ⊓ centralizer (K : Set G) := hcore ▸ hiC
  by_contra hbad
  obtain ⟨_, hX, a, ha, hact, hB, heKB⟩ :=
    source_a6_marked_pumpup_invariant c hG hempty hgen hb hstar eK
      t i ht htC htZ hi hiYK.1 hiYK.2 hbad
  obtain ⟨eKB⟩ := heKB
  let Gi := centralizer ({i} : Set G)
  let D := K.subgroupOf Gi
  let X := componentOrbit D (oddELayer Gi)
  let B := (D.subgroupOf X).subgroupOf a.fixedSubgroup
  let : IsQuasisimple X := hX.2
  let : IsQuasisimple B := hB.2.2
  have hKi : K ≤ Gi := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hiYK.2 k hk)
  let f : X →* G := Gi.subtype.comp X.subtype
  have hf : Function.Injective f := Gi.subtype_injective.comp X.subtype_injective
  have hKX : K ≤ X.map Gi.subtype := by
    intro k hk
    exact ⟨⟨k, hKi hk⟩, le_componentOrbit D (oddELayer Gi) hk, rfl⟩
  have terminal (C : Subgroup a.fixedSubgroup) (hBC : B ≤ C)
      (eC : C ≃* Equiv.Perm (Fin 6)) : False := by
    let j : a.fixedSubgroup →* G := f.comp a.fixedSubgroup.subtype
    have hj : Function.Injective j := hf.comp a.fixedSubgroup.subtype_injective
    let W := C.map j
    have hKW : K ≤ W := by
      intro k hk
      let x : X := ⟨⟨k, hKi hk⟩, le_componentOrbit D (oddELayer Gi) hk⟩
      have hxD : x ∈ D.subgroupOf X := hk
      have hxf : x ∈ a.fixedSubgroup := hB.1 hxD
      exact ⟨⟨x, hxf⟩, hBC hxD, rfl⟩
    have hWt : W ≤ centralizer ({t} : Set G) := by
      rintro w ⟨v, hv, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun y : X => f y)
        ((MulAut.mem_fixedSubgroup a v.val).mp v.property)
      change ((a v.val : Gi) : G) = ((v.val : Gi) : G) at hh
      rw [hact] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    let ew : W ≃* Equiv.Perm (Fin 6) :=
      (C.equivMapOfInjective j hj).symm.trans eC
    exact source_nonfull_a6_symmetric_six_false c hG hempty hgen hb hstar eK hQ
      t ht htC htZ W hKW hWt ew
  have terminal_fixed (e : a.fixedSubgroup ≃* Equiv.Perm (Fin 6)) : False :=
    terminal ⊤ le_top (topEquiv.trans e)
  have hm := source_a6_overcomponent_quotient c hG hempty hgen hb i hi X hX
    a ha B hB.2 eKB eK
  rcases hm with hA8 | hPSL5 | hSp4 | hHS
  · obtain ⟨e⟩ := hA8
    let E := B.map a.fixedSubgroup.subtype
    have hE : E ≤ a.fixedSubgroup := map_subtype_le _
    let eE : E ≃* AlternatingSix.ShadowLocal.A6 :=
      (B.equivMapOfInjective a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective).symm.trans
        (eKB.symm.trans eK)
    obtain ⟨d⟩ := BinaryFixed.alternating_eight_fixed_equiv_symmetric_six e a ha E hE eE
    exact terminal_fixed d
  · let E := B.map a.fixedSubgroup.subtype
    have hE : E ≤ a.fixedSubgroup := map_subtype_le _
    let eE : E ≃* AlternatingSix.ShadowLocal.A6 :=
      (B.equivMapOfInjective a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective).symm.trans
        (eKB.symm.trans eK)
    obtain ⟨d⟩ := BinaryFixed.binary_quotient_fixed_equiv_symmetric_six (Or.inr hPSL5) a ha E hE eE
    exact terminal_fixed d
  · obtain ⟨F, hField, hFinite, hChar, hF, e, hmark⟩ := hSp4
    obtain ⟨d⟩ := symplectic_four_quotient_fixed_equiv_symmetric_six hF a e hmark
    exact terminal_fixed d
  · obtain ⟨e, hmark⟩ := hHS
    obtain ⟨hR, _, hiZ⟩ := source_nonfull_a6_core_four c hG hempty hgen hb hstar eK hQ
      t i ht hi hti htC hiC htZ
    have hR' : (Y ⊓ centralizer (K : Set G)) ⊓ Gi = zpowers t ⊔ zpowers i := by
      rw [← hcore]
      exact hR
    have hSylow := source_nonfull_a6_core_four_sylow c hG hempty hgen hb hstar eK hQ
      t i ht hi hti htC hiC htZ
    have hSylow' : Chapter1.IsSylowIn 2 (zpowers t ⊔ zpowers i)
        ((centralizer ({t} : Set G) ⊓ centralizer (K : Set G)) ⊓ Gi) := by
      rw [← hR]
      exact hSylow
    have hz := source_hs_center_eq_bot c hG hempty hgen hb hstar eK
      t i ht htC htZ hi hiYK hiZ hR' hSylow' X hX hKX e a hact hmark
    obtain ⟨C, hBC, heC⟩ := HSFixed.exists_symmetric_six_overgroup hz e a hmark B
    obtain ⟨eC⟩ := heC
    exact terminal C hBC eC

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
