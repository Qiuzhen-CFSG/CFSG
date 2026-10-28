module
public import Theory.Representation.G2OrthogonalCover.SylowFlag.Uniqueness
public import Theory.Representation.G2BinaryFlagNormalization
public import Theory.Representation.G2BinaryPlaneHyperplaneSpan
/-!
# The unique three-space for the actual derived binary G₂ Sylow

A nonzero fixed vector in the quotient by the unique first line puts the
unique invariant plane inside every invariant space of dimension at least
two. For an invariant three-space, the remaining one-dimensional quotient
is fixed. The actual E and FD root actors then force its vectors into the
coordinate seed. Equality follows from dimension three.

Only fixed-vector theory and two explicit coordinate actions are used;
no enumeration of the 1,395 three-spaces enters the proof. This supplies
the third step of the original flag in Notation13.3.3 and 13.3.18,
Aschbacher–Smith, printed pp.885 and894–895.
-/

public section
noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.SylowFlag
open Subgroup Representation Representation.OneCohomology
open Atlas.G2.Restricted.NaturalCoordinates
open scoped IsMulCommutative commutatorElement
local notation "F" => ZMod 2

private theorem fixed_vector {J V:Type*} [Group J] [Finite J]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (hp:IsPGroup 2 J) (ρ:Representation F J V) :
    ∃v:V,v≠0∧∀j:J,ρ j v=v := by
  exact pGroup_fix_nonzero_vector (by rw [ringChar.eq F 2];decide)
    (by simpa only [ringChar.eq F 2] using hp) ρ

/-- Every derived-Sylow invariant subspace of dimension at least two
contains the actual marked plane. -/
theorem naturalPlane_le_of_invariant_binary (S:Submodule F (Space F))
    (hS:∀g:U F,S≤S.comap (derivedAction F g.val))
    (hdim:2≤Module.finrank F S) : naturalPlane F≤S := by
  have hNS:N1 F≤S:=N1_le_of_invariant F S hS (by
    intro he
    rw [he,finrank_bot] at hdim
    omega)
  let σ:=Representation.subrepresentation ((derivedAction F).comp (U F).subtype) S hS
  let N:Submodule F S:=(N1 F).comap S.subtype
  have hN (g:U F):N≤N.comap (σ g):=fun x hx=>N1_invariant F g hx
  have hdN:Module.finrank F N=1:=
    (Submodule.comapSubtypeEquivOfLe hNS).finrank_eq.trans (N1_finrank F)
  have hdQ:0<Module.finrank F (S⧸N):=by
    have hh:=N.finrank_quotient_add_finrank
    omega
  let : Nontrivial (S⧸N):=Module.nontrivial_of_finrank_pos hdQ
  obtain ⟨q,hq,hqfixed⟩:=fixed_vector (U_isTwoGroup F) (Representation.quotient σ N hN)
  obtain ⟨x,rfl⟩:=N.mkQ_surjective q
  have hxN:x.val∉N1 F:=by
    intro hx
    apply hq
    exact (Submodule.Quotient.mk_eq_zero N).mpr hx
  have hxP:x.val∈naturalPlane F := by
    apply (displacement_mem_N1_iff F x.val).mp
    intro g
    have hh:=hqfixed g
    change N.mkQ (σ g x)=N.mkQ x at hh
    rw [←sub_eq_zero,←map_sub,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hh
    exact hh
  have hNB:N1 F≤S⊓naturalPlane F:=le_inf hNS (N1_le_naturalPlane F)
  have hlt:N1 F<S⊓naturalPlane F:=lt_of_le_of_ne hNB (by
    intro he
    apply hxN
    rw [he]
    exact ⟨x.prop,hxP⟩)
  have hdB:Module.finrank F (S⊓naturalPlane F:Submodule F (Space F))=2 := by
    have hl:=Submodule.finrank_lt_finrank_of_lt hlt
    have hh:=Submodule.finrank_mono (show S⊓naturalPlane F≤naturalPlane F from inf_le_right)
    rw [N1_finrank] at hl
    rw [naturalPlane_finrank] at hh
    omega
  have he:S⊓naturalPlane F=naturalPlane F:=Submodule.eq_of_le_of_finrank_eq inf_le_right
    (hdB.trans (naturalPlane_finrank F).symm)
  exact he ▸ (show S⊓naturalPlane F≤S from inf_le_left)

private theorem one_dimensional_trivial {J V:Type*} [Group J] [Finite J]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hp:IsPGroup 2 J) (ρ:Representation F J V) (hdim:Module.finrank F V=1) :
    ∀j v,ρ j v=v := by
  let : Nontrivial V:=Module.nontrivial_of_finrank_pos (show 0<Module.finrank F V by omega)
  obtain ⟨x,hx,hfix⟩:=fixed_vector hp ρ
  intro j v
  obtain ⟨a,rfl⟩:=(finrank_eq_one_iff_of_nonzero' x hx).mp hdim v
  rw [map_smul,hfix]

/-- The two explicit derived actors E and FD detect the third coordinate
flag step by their displacement modulo the marked plane. -/
theorem seed_of_displacement_in_plane (x:Space F)
    (hx:∀g:U F,derivedAction F g.val x-x∈naturalPlane F) :
    coord F x∈BinaryPointFlag.seed := by
  obtain ⟨a,b,he⟩:=(mem_naturalPlane F _).mp (hx (actorE F))
  obtain ⟨c,d,hh⟩:=(mem_naturalPlane F _).mp (hx (actorH F))
  rw [map_sub,coordinates_action] at he hh
  have h4:=congrFun he 3
  have h5:=congrFun hh 4
  have h3:=congrFun hh 2
  change Restricted.NaturalCoordinates.action F (rootE 1) (coord F x) 3-coord F x 3=0 at h4
  change Restricted.NaturalCoordinates.action F (⁅weylR,rootD (1:F)⁆) (coord F x) 4-coord F x 4=0 at h5
  change Restricted.NaturalCoordinates.action F (⁅weylR,rootD (1:F)⁆) (coord F x) 2-coord F x 2=0 at h3
  rw [commutator_word] at h5 h3
  simp [map_mul,Module.End.mul_apply] at h4 h5 h3
  rw [BinaryPointFlag.mem_seed]
  exact ⟨by simpa [h5] using h3,h4,h5⟩

/-- The unique three-space invariant under the actual derived binary Sylow
is the original coordinate seed. -/
theorem invariant_three_unique_binary (S:Submodule F (Space F))
    (hS:∀g:U F,S≤S.comap (derivedAction F g.val))
    (hdim:Module.finrank F S=3) :
    S=BinaryPointFlag.seed.comap (coord F).toLinearMap := by
  have hPS:naturalPlane F≤S:=naturalPlane_le_of_invariant_binary S hS (by omega)
  let σ:=Representation.subrepresentation ((derivedAction F).comp (U F).subtype) S hS
  let P:Submodule F S:=(naturalPlane F).comap S.subtype
  have hP (g:U F):P≤P.comap (σ g):=fun x hx=>naturalPlane_invariant F g hx
  have hdP:Module.finrank F P=2:=
    (Submodule.comapSubtypeEquivOfLe hPS).finrank_eq.trans (naturalPlane_finrank F)
  have hdQ:Module.finrank F (S⧸P)=1:=by
    have hh:=P.finrank_quotient_add_finrank
    omega
  have htriv:=one_dimensional_trivial (U_isTwoGroup F) (Representation.quotient σ P hP) hdQ
  have hle:S≤BinaryPointFlag.seed.comap (coord F).toLinearMap := by
    intro x hx
    apply seed_of_displacement_in_plane
    intro g
    have hh:=htriv g (P.mkQ ⟨x,hx⟩)
    change P.mkQ (σ g ⟨x,hx⟩)=P.mkQ ⟨x,hx⟩ at hh
    rw [←sub_eq_zero,←map_sub,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hh
    exact hh
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hdim]
  have hd:Module.finrank F BinaryPointFlag.seed=
      Module.finrank F (BinaryPointFlag.seed.comap (coord F).toLinearMap) := by
    have hh:=(coord F).finrank_map_eq (BinaryPointFlag.seed.comap (coord F).toLinearMap)
    rwa [Submodule.map_comap_eq_of_surjective (coord F).surjective] at hh
  rw [←hd]
  have hc:=Module.natCard_eq_pow_finrank (K:=F) (V:=BinaryPointFlag.seed)
  rw [BinaryPointFlag.card_seed,Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide:1<(2:ℕ)) hc
end Atlas.G2.Natural.OrthogonalCover.SylowFlag
