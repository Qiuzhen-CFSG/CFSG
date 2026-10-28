module
public import Theory.SpecificGroups.PSL2.ThompsonBorel

/-!
# Thompson containment for binary linear components

The elementary Sylow of PSL₂(2ⁿ), n ≥ 2, has order at least that of every
elementary subgroup of its automorphism group. Maximum-elementary
replacement puts it inside J of every normalizing overgroup. For a relative
component whose normalizer has index at most two in S, paired-component
replacement first shows that J(S) normalizes the component. Thompson heredity
then gives the same Sylow containment for S, including the exceptional field
of four elements.
Source: Aschbacher--Smith 15.1.21(i),(ii), printed pp.1097--1098.
-/

public section
open Subgroup
namespace Theory.PSL2.OrdinaryBorel
variable {G : Type*} [_root_.Group G] [Finite G]

/-- The component Sylow lies in the Thompson subgroup of a normalizing overgroup. -/
theorem normalizing_thompson_contains_sylow (L Q : Subgroup G)
    (hQL : Q ≤ normalizer (L : Set G)) (P : Sylow 2 L)
    (hPQ : (P : Subgroup L).map L.subtype ≤ Q)
    {n : ℕ} (hn : 2≤n) (e : L ≃* BinaryGroup n) :
    (P : Subgroup L).map L.subtype ≤ Stellmacher.elementaryAbelianMaxJ Q := by
  let f : Q →* MulAut (BinaryGroup n) := (MulAut.congr e).toMonoidHom.comp
    (L.normalizerMonoidHom.comp (inclusion hQL))
  let U := (P : Subgroup L).map L.subtype
  let W := U.subgroupOf Q
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let eP : P ≃* R := e.subgroupMap (P : Subgroup L)
  let : IsElementaryAbelian 2 R := sylow_elementary R
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hPQ
  have hcardP : Nat.card P=2^n := (Nat.card_congr eP.toEquiv).trans
    ((sylow_card R).trans (GaloisField.card 2 n (by omega)))
  have hcardW : Nat.card W=2^n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPQ).toEquiv,
      card_map_of_injective L.subtype_injective,hcardP]
  have hfon (l : L) (hl : (l:G) ∈ Q) : f ⟨l,hl⟩=MulAut.conj (e l) := by
    ext y
    change e (L.normalizerMonoidHom ⟨l,hQL hl⟩ (e.symm y))=e l*y*(e l)⁻¹
    change e (l*(e.symm y)*l⁻¹)=_
    rw [map_mul,map_mul,map_inv,e.apply_symm_apply]
  have hker (x : Q) : x ∈ f.ker ↔ (x:G) ∈ centralizer (L:Set G) := by
    change MulAut.congr e (L.normalizerMonoidHom ⟨x,hQL x.property⟩)=1 ↔ _
    rw [←(MulAut.congr e).map_one,(MulAut.congr e).injective.eq_iff]
    change (⟨x,hQL x.property⟩:normalizer (L:Set G)) ∈ L.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hWker : Disjoint W f.ker := by
    apply disjoint_def.mpr
    intro w hw hk
    obtain ⟨l,hl,he⟩ := hw
    have hwe : (⟨l,hPQ (mem_map_of_mem L.subtype hl)⟩:Q)=w := Subtype.ext he
    have hh : MulAut.conj (e l)=1 := (hfon l _).symm.trans (hwe ▸ hk)
    have heone : e l=1 := psl2_conj_eq_one_implies (e l) hh
    have hlone : l=1 := e.injective (heone.trans e.map_one.symm)
    apply Subtype.ext
    exact he.symm.trans (congrArg (fun l : L => (l:G)) hlone)
  have hWC (A : Subgroup Q) : W ≤ centralizer (A⊓f.ker : Set Q) := by
    intro w hw a ha
    obtain ⟨l,hl,he⟩ := hw
    have hh := (hker a).mp ha.2
    apply Subtype.ext
    change (a:G)*(w:G)=(w:G)*(a:G)
    have he' : (l:G)=(w:G) := he
    rw [←he']
    exact (hh l l.property).symm
  have himageW : Nat.card (W.map f)=2^n := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map W f
    rw [hWker.eq_bot,card_bot,one_mul,hcardW] at hh
    exact hh
  have hWJ : W ≤ Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup Q) := by
    obtain ⟨A,hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (⊤:Subgroup Q)
    let : IsElementaryAbelian 2 A := hA.2.1
    let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
    apply Stellmacher.elementary_le_maxJ_of_image_bound ⊤ A W f hA le_top (hWC A) hWker
    rw [hcardW]
    exact elementary_card_le (by omega) (A.map f)
  have hJmap : (Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup Q)).map Q.subtype =
      Stellmacher.elementaryAbelianMaxJ Q := by
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective Q.subtype Q.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hPJ : U ≤ Stellmacher.elementaryAbelianMaxJ Q := by
    have hh := map_mono (f:=Q.subtype) hWJ
    rwa [map_subgroupOf_eq_of_le hPQ,hJmap] at hh
  exact hPJ

/-- The original Thompson subgroup normalizes the relative component. -/
theorem component_thompson_normalizes
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : Theory.GroupTheory.IsComponent H (L.subgroupOf H))
    (hi : (normalizer (L:Set G)).relIndex S ≤ 2)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    {n : ℕ} (hn : 2≤n) (e : L ≃* BinaryGroup n) :
    Stellmacher.elementaryAbelianMaxJ S ≤ normalizer (L:Set G) := by
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let eP : P ≃* R := e.subgroupMap (P : Subgroup L)
  let : IsElementaryAbelian 2 R := sylow_elementary R
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  have hcardP : Nat.card P=2^n := (Nat.card_congr eP.toEquiv).trans
    ((sylow_card R).trans (GaloisField.card 2 n (by omega)))
  have hp : 2<Nat.card P := by
    rw [hcardP]
    exact (by decide : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  have hz : center L=⊥ := by
    apply bot_unique
    intro l hl
    have hh : e l ∈ center (BinaryGroup n) := (centerCongr e ⟨l,hl⟩).property
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact mem_bot.mpr (e.injective (hh.trans e.map_one.symm))
  have hb (D : Subgroup (MulAut L)) (hD : IsElementaryAbelian 2 D) : Nat.card D ≤ Nat.card P := by
    let := hD
    let eA := MulAut.congr e
    let : IsElementaryAbelian 2 (D.map eA.toMonoidHom) := IsElementaryAbelian.map eA.toMonoidHom
    have hh := elementary_card_le (by omega : 2≤n) (D.map eA.toMonoidHom)
    rwa [card_map_of_injective eA.injective,←hcardP] at hh
  have hJN := hL.maxJ_normalizes_of_elementary_sylow_bound H L S hLH hSH hz hi P hPS hp hb
  exact hJN

/-- Component Sylow containment holds even when S exchanges components. -/
theorem component_thompson_contains_sylow
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : Theory.GroupTheory.IsComponent H (L.subgroupOf H))
    (hi : (normalizer (L:Set G)).relIndex S ≤ 2)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    {n : ℕ} (hn : 2≤n) (e : L ≃* BinaryGroup n) :
    (P : Subgroup L).map L.subtype ≤ Stellmacher.elementaryAbelianMaxJ S := by
  have hJN := component_thompson_normalizes H L S hLH hSH hL hi P hPS hn e
  let Q := S ⊓ normalizer (L:Set G)
  have hJ : Stellmacher.elementaryAbelianMaxJ Q=Stellmacher.elementaryAbelianMaxJ S :=
    Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate S Q
      (le_inf (sSup_le fun _ hA => hA.1) hJN) inf_le_left
  rw [←hJ]
  exact normalizing_thompson_contains_sylow L Q inf_le_right P
    (le_inf hPS ((map_subtype_le _).trans L.le_normalizer)) hn e

end Theory.PSL2.OrdinaryBorel
