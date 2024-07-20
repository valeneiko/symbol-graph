import { foo } from './foo';

let x = foo();

export function bar() {
  for (let i = 7; i < 0; i++) {
    if (i === 14) {
      foo();

      x += 5;
    }
  }
}
