module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate.Actions

/-!
# Checked actions of words in the Held representative

The certified packed action tables give fast forward and inverse actions of
the four actual representative generators. The inverse is the third power,
checked on every vertex. Signed word evaluation is then transported through
the actual Held representation. This provides a shared computation boundary
for the four-group normalizer certificates.

Sources: the ATLAS degree-2058 action; GLS3 Table 5.3p; the four-group
inspection in Aschbacher–Smith 15.3.43, printed p.1140.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.WordActions
open Subgroup LocalPairs.SylowGeometry.Calculations
open InnerNormalizer.OrbitCertificate

set_option Elab.async false

set_option maxRecDepth 16384 in
public theorem action_four : ∀ (i : Fin 4) (x : Fin 2058),
    action i (action i (action i (action i x))) = x := by
  decide +kernel

@[expose] public def fastGenerator (i : Fin 4) : Equiv.Perm (Fin 2058) where
  toFun := action i
  invFun x := action i (action i (action i x))
  left_inv := action_four i
  right_inv := action_four i

public theorem fastGenerator_eq (i : Fin 4) : fastGenerator i = representation (generator i) :=
  Equiv.ext (action_eq i)

@[expose] public def fastLetter (k : ℤ) : Equiv.Perm (Fin 2058) :=
  let g := fastGenerator (Fin.ofNat 4 (k.natAbs - 1))
  if k < 0 then g⁻¹ else g

public theorem fastLetter_eq (k : ℤ) : fastLetter k = representation (letter k : He) := by
  unfold fastLetter letter
  split
  · rw [fastGenerator_eq]
    rfl
  · rw [fastGenerator_eq]

@[expose] public def fastWord (w : List ℤ) : Equiv.Perm (Fin 2058) := (w.map fastLetter).prod

public theorem fastWord_eq (w : List ℤ) : fastWord w = representation (word w : He) := by
  change (w.map fastLetter).prod =
    (representation.comp representative.subtype) ((w.map letter).prod)
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left (fun k _ => fastLetter_eq k)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.WordActions
