# Theory cleanup

## Brief

Make `Theory` reusable and independent of `FeitThompson`: move duplicated generic declarations into
`Theory.*` namespaces/modules, remove compatibility wrappers and re-exports, and update downstream
imports explicitly.

## Resume

- route: audit the five remaining `Theory` imports of `FeitThompson`; migrate their generic source
  declarations and namespace all Theory items, then update downstream imports.
- blocker: none recorded.
- next action: replace the first remaining FeitThompson dependency and run a targeted Theory build.
- routes to avoid: retaining compatibility `abbrev`/alias wrappers in FeitThompson modules.

## Progress

- initiated (2026-09-02T05:50:00Z): baseline `lake build Theory` fails because both Theory and
  FeitThompson define `quotientMulDistribMulAction`; five Theory files still import FeitThompson.

## Subnodes

- [ ] migrate elementary-abelian API
- [ ] migrate group-action API
- [ ] migrate representation/endomorphism APIs
- [ ] namespace all remaining Theory declarations
- [ ] update imports and validate full build

## Route Ledger

- observed: `Theory.ElementaryAbelian.Basic` and `Theory.GroupAction.*` already contain the generic
  implementations needed to replace several FeitThompson wrappers.
